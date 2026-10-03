/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.ExpandedAndElliptic

/-! # Harmonic Approximation -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Deterministic homogenization black boxes: harmonic approximation

This file contains the Section 3.3.C corollary surface from
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 3254--3356.

The manuscript states the mesoscopic corollary on cubes `x + □_n`.  In Lean we
state the same result on an arbitrary triadic cube `Q`; callers instantiate
`Q` with the desired subcube.  The current Section 3.3 output is a negative
Besov comparison estimate, exactly as the manuscript notes before deferring the
stronger excess-decay upgrade to the large-scale regularity chapter.
-/

/--
The single flux-defect quantity used by the harmonic-approximation corollary.
It is the Section 3.3.A localized average at depth zero, i.e. the local
negative Besov size of `(a - a₀)∇u` on the cube where the harmonic replacement
is taken.
-/
noncomputable def harmonicApproximationFluxDefectBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (u : AHarmonicFunction a (cubeSet Q)) : ℝ :=
  localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.toH1.grad) 0

/--
The harmonic-approximation flux-defect quantity is the absolute value of the
one-cube negative Besov seminorm of `(a - a₀)∇u`.
-/
@[simp] theorem harmonicApproximationFluxDefectBound_eq_abs_cubeBesovNegativeVectorSeminormTwo
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (u : AHarmonicFunction a (cubeSet Q)) :
    harmonicApproximationFluxDefectBound Q a a0 s u =
      |cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad)| := by
  simp [harmonicApproximationFluxDefectBound]

/--
If the one-cube negative Besov seminorm is known to be nonnegative, the
harmonic-approximation flux-defect package is exactly that seminorm.
-/
theorem harmonicApproximationFluxDefectBound_eq_cubeBesovNegativeVectorSeminormTwo_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (hdefect_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad)) :
    harmonicApproximationFluxDefectBound Q a a0 s u =
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) := by
  rw [harmonicApproximationFluxDefectBound_eq_abs_cubeBesovNegativeVectorSeminormTwo]
  exact abs_of_nonneg hdefect_nonneg

/--
Exact harmonic-approximation comparison from the local flux-defect quantity,
assuming the comparison pair has already been packaged.

This is the clean deterministic corollary surface behind
`c.harmonic.approximation.negative.norm.deterministic.theory`, manuscript lines
3294--3348, in cube-normalized notation.
-/
theorem solution_l2_close_harmonic_of_harmonicApproximationFluxDefectBound_of_comparisonPair
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 u.toH1.grad v.toH1.grad) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ *
          harmonicApproximationFluxDefectBound Q a a0 s u := by
  subst a0
  simpa [harmonicApproximationFluxDefectBound] using
    solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
      hdual Q a sigma0 u.toH1.grad v.toH1.grad 0 hsigma0 hs_pos hs_lt_one hEll
      hcomparison

/--
Exact harmonic-approximation comparison from the local flux-defect quantity.

This is the clean deterministic corollary surface behind
`c.harmonic.approximation.negative.norm.deterministic.theory`, manuscript lines
3294--3348, in cube-normalized notation.  The boundary condition is the
manuscript hypothesis `u - v ∈ H¹₀`, represented here by zero-trace
potentiality of `∇u - ∇v`; harmonicity supplies the solenoidal comparison
identity.
-/
theorem solution_l2_close_harmonic_of_harmonicApproximationFluxDefectBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x)) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ *
          harmonicApproximationFluxDefectBound Q a a0 s u :=
    solution_l2_close_harmonic_of_harmonicApproximationFluxDefectBound_of_comparisonPair
      hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
        (IsHomogenizationComparisonPairOn.of_aHarmonicFunctions hEll ha0 u v hzeroTrace)

/--
Downstream-facing harmonic-approximation bound from an already packaged
comparison pair.

This variant is useful for lower-level deterministic plumbing.  Most callers
should prefer `solution_l2_close_harmonic_of_fluxDefectBound`, whose boundary
input is the manuscript zero-trace condition.
-/
theorem solution_l2_close_harmonic_of_fluxDefectBound_of_comparisonPair
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 u.toH1.grad v.toH1.grad)
    (hfluxDefectBound :
      harmonicApproximationFluxDefectBound Q a a0 s u ≤ fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound := by
    calc
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad
          ≤ Cdual * s⁻¹ *
              harmonicApproximationFluxDefectBound Q a a0 s u :=
        solution_l2_close_harmonic_of_harmonicApproximationFluxDefectBound_of_comparisonPair
          hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
          hcomparison
      _ ≤ Cdual * s⁻¹ * fluxDefectBound := by
          exact mul_le_mul_of_nonneg_left hfluxDefectBound
            (mul_nonneg hdual.1 (inv_nonneg.mpr hs_pos.le))

/--
Downstream-facing harmonic-approximation apex for
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 3294--3348.

Probabilistic or iteration-loop callers only need to prove the single
hypothesis `hfluxDefectBound`, namely a bound on
`harmonicApproximationFluxDefectBound`.  The qualitative ellipticity
parameters certify the coefficient classes but do not appear quantitatively in
the conclusion.
-/
theorem solution_l2_close_harmonic_of_fluxDefectBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hfluxDefectBound :
      harmonicApproximationFluxDefectBound Q a a0 s u ≤ fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound := by
    exact
      solution_l2_close_harmonic_of_fluxDefectBound_of_comparisonPair
        hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
          (IsHomogenizationComparisonPairOn.of_aHarmonicFunctions hEll ha0 u v hzeroTrace)
          hfluxDefectBound

/--
Downstream-facing harmonic-approximation apex from a direct one-cube negative
Besov bound on the flux defect `(a - a₀)∇u`.

This is the same statement as
`solution_l2_close_harmonic_of_fluxDefectBound`, with the Section 3.3.C
depth-zero flux-defect package unfolded using
`harmonicApproximationFluxDefectBound_eq_abs_cubeBesovNegativeVectorSeminormTwo`.
-/
theorem solution_l2_close_harmonic_of_cubeBesovNegativeFluxDefectBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hfluxDefectBound :
      |cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad)| ≤
        fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound := by
    exact
      solution_l2_close_harmonic_of_fluxDefectBound
        hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hzeroTrace
        (by simpa using hfluxDefectBound)

/--
Downstream-facing harmonic-approximation apex from a direct one-cube negative
Besov bound, with the usual nonnegativity of the seminorm supplied separately.

This keeps Ch3 independent of any future convenience lemma that may derive
nonnegativity from stronger integrability hypotheses.
-/
theorem solution_l2_close_harmonic_of_cubeBesovNegativeFluxDefectBound_of_nonneg
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hdefect_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad))
    (hfluxDefectBound :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) ≤
        fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound := by
    exact
      solution_l2_close_harmonic_of_fluxDefectBound
        hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hzeroTrace
        (by
        rw [harmonicApproximationFluxDefectBound_eq_cubeBesovNegativeVectorSeminormTwo_of_nonneg
          Q a a0 s u hdefect_nonneg]
        exact hfluxDefectBound)

/--
The explicit RHS-final-theorem flux-defect bound from
`CoarsePoincareRHS.FinalTheorems.ExpandedAndElliptic`, packaged for direct
Section 3.3.C composition.

Only the scale-local `lambdaSq` quantity appears here; the qualitative
uniform ellipticity witnesses remain hypotheses of the theorem that supplies
the bound.
-/
noncomputable def coarsePoincareRHSFinalFluxDefectBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g defect : Vec d → Vec d) (s : ℝ) : ℝ :=
  Real.sqrt
    (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        cubeAverage Q (coefficientEnergyDensity a defect) +
      15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

/--
Direct Section 3.3.C composition with the RHS-side final theorem
`cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal`.

This is the explicit wrapper deferred in the blocker memo: callers supply the
potential/solenoidal hypotheses for the actual flux defect
`(a - a₀)∇u`, and the theorem feeds the resulting q=2 bound through the
harmonic-approximation black box from manuscript lines 3294--3348.
-/
theorem solution_l2_close_harmonic_of_coarsePoincareRHSFinalFluxDefectBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (g : Vec d → Vec d)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_le_one : s ≤ 1) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hdefect_potential :
      IsPotentialOn (cubeSet Q) (fluxDefect a a0 u.toH1.grad))
    (hdefect_residual :
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (a x) (fluxDefect a a0 u.toH1.grad x) - g x))
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ *
          coarsePoincareRHSFinalFluxDefectBound Q a g (fluxDefect a a0 u.toH1.grad) s := by
  have hdefectMemL2 :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 u.toH1.grad) := by
    rcases hdefect_potential with ⟨w, hw⟩
    simpa [← hw] using w.grad_memVectorL2
  have hdefectMemLp :
      MeasureTheory.MemLp (fluxDefect a a0 u.toH1.grad) (2 : ENNReal)
        (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hdefectMemL2
  have hdefect_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp
      Q hs_pos (fluxDefect a a0 u.toH1.grad) hdefectMemLp
  have hfluxDefectBound :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) ≤
        coarsePoincareRHSFinalFluxDefectBound Q a g (fluxDefect a a0 u.toH1.grad) s := by
    simpa [coarsePoincareRHSFinalFluxDefectBound] using
      cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
        (Q := Q) (a := a) (g := g) (u := fluxDefect a a0 u.toH1.grad)
        (s := s) (lam := lam) (Lam := Lam)
        hs_pos hs_le_one hEll hdefect_potential hdefect_residual hg hGlobalBdd
  exact
    solution_l2_close_harmonic_of_cubeBesovNegativeFluxDefectBound_of_nonneg
      hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hzeroTrace
      hdefect_nonneg hfluxDefectBound

/--
The Ch1 q=1-to-q=2 weak-norm bridge converts a finite-depth q=1 flux-defect
bound into the single Section 3.3.C flux-defect quantity.

This is the API bridge needed to compose with q=1 actual flux-response estimates:
the caller supplies the partial q=1 bounds for `(a - a₀)∇u`, and this lemma
packages them as the q=2 local flux-defect bound consumed by the harmonic
approximation corollary.
-/
theorem harmonicApproximationFluxDefectBound_le_of_qonePartialFluxDefectBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (u : AHarmonicFunction a (cubeSet Q)) {s fluxDefectBound : ℝ}
    (hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          fluxDefectBound) :
    harmonicApproximationFluxDefectBound Q a a0 s u ≤ fluxDefectBound := by
  have hq2 :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) ≤
        fluxDefectBound :=
    cubeBesovNegativeVectorSeminormTwo_le_of_qone_partialBound
      Q s (fluxDefect a a0 u.toH1.grad) hpartialFluxDefectBound
  have hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 u.toH1.grad)) := by
    use fluxDefectBound
    rintro x ⟨N, rfl⟩
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm
        Q s N (fluxDefect a a0 u.toH1.grad)).trans (hpartialFluxDefectBound N)
  have hdefect_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) := by
    have hpartial0_le :
        cubeBesovNegativeVectorPartialSeminormTwo Q s 0
            (fluxDefect a a0 u.toH1.grad) ≤
          cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.toH1.grad) := by
      unfold cubeBesovNegativeVectorSeminormTwo
      exact le_csSup hBdd ⟨0, rfl⟩
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_nonneg
        Q s 0 (fluxDefect a a0 u.toH1.grad)).trans hpartial0_le
  rw [harmonicApproximationFluxDefectBound_eq_cubeBesovNegativeVectorSeminormTwo_of_nonneg
    Q a a0 s u hdefect_nonneg]
  exact hq2

/--
Harmonic-approximation comparison from q=1 finite-depth flux-defect bounds,
with the comparison pair already packaged.

This wrapper is for direct composition with q=1 actual flux-response estimates
once they expose their finite-depth partial-bound form.  It is still the
Section 3.3.C deterministic comparison from manuscript lines 3294--3348; the
new input is only a q=1 presentation of the same local flux-defect bound.
-/
theorem solution_l2_close_harmonic_of_qonePartialFluxDefectBound_of_comparisonPair
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 u.toH1.grad v.toH1.grad)
    (hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound := by
    exact
      solution_l2_close_harmonic_of_fluxDefectBound_of_comparisonPair
        hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hcomparison
        (harmonicApproximationFluxDefectBound_le_of_qonePartialFluxDefectBound
          Q a a0 u hpartialFluxDefectBound)

/--
Harmonic-approximation comparison from q=1 finite-depth flux-defect bounds.

This is the zero-trace-facing version of
`solution_l2_close_harmonic_of_qonePartialFluxDefectBound_of_comparisonPair`.
It keeps the Section 3.3.C headline API compatible with q=1 actual
flux-response inputs while preserving the same qualitative ellipticity surface.
-/
theorem solution_l2_close_harmonic_of_qonePartialFluxDefectBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound :=
    solution_l2_close_harmonic_of_qonePartialFluxDefectBound_of_comparisonPair
      hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
      (IsHomogenizationComparisonPairOn.of_aHarmonicFunctions hEll ha0 u v hzeroTrace)
      hpartialFluxDefectBound

/--
Convert a full q=1 flux-defect bound into the Section 3.3.C q=2 flux-defect
package, assuming the finite-depth q=1 seminorms are bounded above.

The boundedness hypothesis is the standard condition needed to compare a
finite partial seminorm with its `sSup` definition.  When the caller already
has finite-depth q=1 bounds, prefer
`harmonicApproximationFluxDefectBound_le_of_qonePartialFluxDefectBound`, which
does not need this extra boundedness witness.
-/
theorem harmonicApproximationFluxDefectBound_le_of_qoneFluxDefectBound_of_partialSeminorm_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (u : AHarmonicFunction a (cubeSet Q)) {s fluxDefectBound : ℝ}
    (hpartialBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad)))
    (hqoneFluxDefectBound :
      cubeBesovNegativeVectorSeminorm Q s (fluxDefect a a0 u.toH1.grad) ≤
        fluxDefectBound) :
    harmonicApproximationFluxDefectBound Q a a0 s u ≤ fluxDefectBound := by
  have hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          fluxDefectBound := by
    intro N
    have hpartial_le_full :
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          cubeBesovNegativeVectorSeminorm Q s (fluxDefect a a0 u.toH1.grad) := by
      unfold cubeBesovNegativeVectorSeminorm
      exact le_csSup hpartialBdd ⟨N, rfl⟩
    exact hpartial_le_full.trans hqoneFluxDefectBound
  exact
    harmonicApproximationFluxDefectBound_le_of_qonePartialFluxDefectBound
      Q a a0 u hpartialFluxDefectBound

/--
Harmonic-approximation comparison from a full q=1 flux-defect bound, plus the
boundedness witness needed to unfold the q=1 supremum.

This is useful when a previous theorem exposes only the full q=1 seminorm
bound.  It is intentionally weaker than the finite-depth partial-bound wrapper
above, because the extra boundedness hypothesis is mathematically required by
the `sSup` API.
-/
theorem solution_l2_close_harmonic_of_qoneFluxDefectBound_of_partialSeminorm_bddAbove
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s fluxDefectBound : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hpartialBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad)))
    (hqoneFluxDefectBound :
      cubeBesovNegativeVectorSeminorm Q s (fluxDefect a a0 u.toH1.grad) ≤
        fluxDefectBound) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * fluxDefectBound :=
    solution_l2_close_harmonic_of_fluxDefectBound
      hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hzeroTrace
      (harmonicApproximationFluxDefectBound_le_of_qoneFluxDefectBound_of_partialSeminorm_bddAbove
        Q a a0 u hpartialBdd hqoneFluxDefectBound)

/--
The q=1 actual flux-response right-hand side for a harmonic field, matching the
bound proved by `coarseFluxResponse_qone_of_aHarmonicFunction`.

This is kept in the black-box namespace as a composition target: if the
coarse-flux-response side exposes the same finite-depth q=1 partial bound, the
harmonic approximation theorem below consumes it without re-bundling.
-/
noncomputable def qoneCoarseFluxResponseBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : AHarmonicFunction a (cubeSet Q)) : ℝ :=
  (geometricDiscount s 1)⁻¹ *
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
      (Real.sqrt (((4 : ℝ) * matNorm a0)) *
        Real.sqrt (cubeAverage Q (scalarVariationEnergyIntegrand a u)))

/--
Direct Section 3.3.C composition with
`coarseFluxResponse_qone_of_aHarmonicFunction`.

The upstream theorem currently exposes the full q=1 seminorm bound, so this
wrapper keeps the boundedness witness needed to compare finite q=1 partial
seminorms with that supremum.  Callers that have finite-depth q=1 estimates
can continue to use
`solution_l2_close_harmonic_of_qoneCoarseFluxResponsePartialBound`.
-/
theorem solution_l2_close_harmonic_of_coarseFluxResponse_qone_of_aHarmonicFunction
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hpartialBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad)))
    (hsum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * qoneCoarseFluxResponseBound Q a a0 s u := by
  have hqone :
      cubeBesovNegativeVectorSeminorm Q s (fluxDefect a a0 u.toH1.grad) ≤
        qoneCoarseFluxResponseBound Q a a0 s u := by
    simpa [fluxDefect, qoneCoarseFluxResponseBound] using!
      coarseFluxResponse_qone_of_aHarmonicFunction
        (Q := Q) (a := a) (a0 := a0) (s := s)
        hs_pos hEll ha0 ha0symm u hsum
  exact
    solution_l2_close_harmonic_of_qoneFluxDefectBound_of_partialSeminorm_bddAbove
      hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hzeroTrace
      hpartialBdd hqone

/--
Convert the q=1 finite-depth actual flux-response estimate into the Section
3.3.C flux-defect package.

The right-hand side is definitionally the q=1 response bound from
`coarseFluxResponse_qone_of_aHarmonicFunction`; the only requested input is the
finite-depth version of that estimate, because the q=2 black-box consumes the
supremum through the Ch1 q=1-to-q=2 bridge.
-/
theorem harmonicApproximationFluxDefectBound_le_qoneCoarseFluxResponseBound_of_partialFluxDefectBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (u : AHarmonicFunction a (cubeSet Q)) {s : ℝ}
    (hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          qoneCoarseFluxResponseBound Q a a0 s u) :
    harmonicApproximationFluxDefectBound Q a a0 s u ≤
      qoneCoarseFluxResponseBound Q a a0 s u :=
  harmonicApproximationFluxDefectBound_le_of_qonePartialFluxDefectBound
    Q a a0 u hpartialFluxDefectBound

/--
Harmonic-approximation comparison with the q=1 actual flux-response RHS,
assuming the comparison pair has already been packaged.

This is the direct Section 3.3.C composition surface for q=1 actual
flux-response inputs: finite-depth q=1 defect control is converted to the q=2
local flux-defect package and then fed through the deterministic comparison
theorem from manuscript lines 3294--3348.
-/
theorem solution_l2_close_harmonic_of_qoneCoarseFluxResponsePartialBound_of_comparisonPair
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 u.toH1.grad v.toH1.grad)
    (hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          qoneCoarseFluxResponseBound Q a a0 s u) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * qoneCoarseFluxResponseBound Q a a0 s u := by
    exact
      solution_l2_close_harmonic_of_qonePartialFluxDefectBound_of_comparisonPair
        hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm hcomparison
        hpartialFluxDefectBound

/--
Harmonic-approximation comparison with the q=1 actual flux-response RHS.

This zero-trace-facing wrapper is the black-box endpoint to use once the
coarse-flux-response side supplies finite-depth q=1 bounds for the actual
defect `(a - a₀)∇u`.
-/
theorem solution_l2_close_harmonic_of_qoneCoarseFluxResponsePartialBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hpartialFluxDefectBound :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N (fluxDefect a a0 u.toH1.grad) ≤
          qoneCoarseFluxResponseBound Q a a0 s u) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        Cdual * s⁻¹ * qoneCoarseFluxResponseBound Q a a0 s u :=
    solution_l2_close_harmonic_of_qoneCoarseFluxResponsePartialBound_of_comparisonPair
      hdual Q a a0 sigma0 u v hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
      (IsHomogenizationComparisonPairOn.of_aHarmonicFunctions hEll ha0 u v hzeroTrace)
      hpartialFluxDefectBound

/--
Homogeneous coarse-graining bound from manuscript lines 3264--3292 for an
arbitrary `H¹` function, written as the flux-defect quantity predicted by the
previous coarse-graining theorem with zero forcing.
-/
noncomputable def homogeneousCoarseGrainingFluxDefectBoundH1 {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : H1Function (cubeSet Q)) : ℝ :=
  (s⁻¹) * Real.sqrt (matNorm a0) *
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 *
      Real.sqrt (cubeAverage Q (coefficientEnergyDensity a u.grad))

/-- The homogeneous `H¹` comparison right-hand side after duality. -/
noncomputable def homogeneousCoarseGrainingRhsH1 {d : ℕ} [NeZero d]
    (Cdual : ℝ)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : H1Function (cubeSet Q)) : ℝ :=
  Cdual * s⁻¹ *
    homogeneousCoarseGrainingFluxDefectBoundH1 Q a a0 s u

/--
The homogeneous `H¹` flux-defect bound is the general Section 3.3.B bound with
depth zero and zero right-hand side.
-/
theorem homogeneousCoarseGrainingFluxDefectBoundH1_eq_coarseGrainingL2FluxDefectBound_zero_forcing
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : H1Function (cubeSet Q)) :
    homogeneousCoarseGrainingFluxDefectBoundH1 Q a a0 s u =
      coarseGrainingL2FluxDefectBound Q a a0 s 0 u.grad (0 : Vec d → Vec d) := by
  rw [coarseGrainingL2FluxDefectBound_depth_zero_zero_forcing]
  rfl

/--
The homogeneous `H¹` comparison RHS is the general Section 3.3.B RHS with depth
zero and zero right-hand side.
-/
theorem homogeneousCoarseGrainingRhsH1_eq_coarseGrainingL2Rhs_zero_forcing
    {d : ℕ} [NeZero d] (Cdual : ℝ)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : H1Function (cubeSet Q)) :
    homogeneousCoarseGrainingRhsH1 Cdual Q a a0 s u =
      coarseGrainingL2Rhs Cdual Q a a0 s 0 u.grad (0 : Vec d → Vec d) := by
  unfold homogeneousCoarseGrainingRhsH1 coarseGrainingL2Rhs
  rw [homogeneousCoarseGrainingFluxDefectBoundH1_eq_coarseGrainingL2FluxDefectBound_zero_forcing]

/--
Manuscript-facing homogeneous coarse-graining corollary for
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 3254--3292.

This is Corollary `c.general.coarse.graining.homogeneous.deterministic.theory`
in the same abstract-composition form as the Section 3.3.B theorem: the local
coarse flux-defect estimate enters as the single hypothesis
`hcoarseFluxDefect`.
-/
theorem solution_diff_l2_le_homogeneousCoarseGrainingRhsH1_of_zeroRhs_of_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u (0 : Vec d → Vec d))
    (hv :
      IsH1DirichletRhsWeakSolutionOn
        (constantCoeffField a0) (cubeSet Q) v (0 : Vec d → Vec d))
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) 0 ≤
        homogeneousCoarseGrainingFluxDefectBoundH1 Q a a0 s u) :
        solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
          homogeneousCoarseGrainingRhsH1 Cdual Q a a0 s u := by
  have _ : IsEllipticMatrix lam0 Lam0 a0 := ha0
  have _ : a0.IsSymm := ha0symm
  have hcoarseFluxDefect' :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.grad) 0 ≤
        coarseGrainingL2FluxDefectBound Q a a0 s 0 u.grad (0 : Vec d → Vec d) := by
    rw [← homogeneousCoarseGrainingFluxDefectBoundH1_eq_coarseGrainingL2FluxDefectBound_zero_forcing]
    exact hcoarseFluxDefect
  calc
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad
        ≤ coarseGrainingL2Rhs Cdual Q a a0 s 0 u.grad (0 : Vec d → Vec d) :=
      solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_of_coarseFluxDefect_le
        hdual Q a a0 sigma0 u v (0 : Vec d → Vec d) 0
        hsigma0 ha0eq hs_pos hs_lt_one hEll hu hv hzeroTrace hcoarseFluxDefect'
    _ = homogeneousCoarseGrainingRhsH1 Cdual Q a a0 s u := by
      rw [← homogeneousCoarseGrainingRhsH1_eq_coarseGrainingL2Rhs_zero_forcing]

/--
Homogeneous coarse-graining bound from manuscript lines 3264--3292, specialized
to an `a`-harmonic function.
-/
noncomputable def homogeneousCoarseGrainingFluxDefectBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : AHarmonicFunction a (cubeSet Q)) : ℝ :=
  homogeneousCoarseGrainingFluxDefectBoundH1 Q a a0 s u.toH1

/-- The homogeneous harmonic-approximation right-hand side after duality. -/
noncomputable def homogeneousCoarseGrainingRhs {d : ℕ} [NeZero d]
    (Cdual : ℝ)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : AHarmonicFunction a (cubeSet Q)) : ℝ :=
  Cdual * s⁻¹ *
    homogeneousCoarseGrainingFluxDefectBound Q a a0 s u

/--
The homogeneous flux-defect bound is the general Section 3.3.B bound with
depth zero and zero right-hand side.
-/
theorem homogeneousCoarseGrainingFluxDefectBound_eq_coarseGrainingL2FluxDefectBound_zero_forcing
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : AHarmonicFunction a (cubeSet Q)) :
    homogeneousCoarseGrainingFluxDefectBound Q a a0 s u =
      coarseGrainingL2FluxDefectBound Q a a0 s 0 u.toH1.grad (0 : Vec d → Vec d) := by
  rw [coarseGrainingL2FluxDefectBound_depth_zero_zero_forcing]
  rfl

/--
The homogeneous comparison RHS is the general Section 3.3.B RHS with depth
zero and zero right-hand side.
-/
theorem homogeneousCoarseGrainingRhs_eq_coarseGrainingL2Rhs_zero_forcing
    {d : ℕ} [NeZero d] (Cdual : ℝ)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (u : AHarmonicFunction a (cubeSet Q)) :
    homogeneousCoarseGrainingRhs Cdual Q a a0 s u =
      coarseGrainingL2Rhs Cdual Q a a0 s 0 u.toH1.grad (0 : Vec d → Vec d) := by
  unfold homogeneousCoarseGrainingRhs coarseGrainingL2Rhs
  rw [homogeneousCoarseGrainingFluxDefectBound_eq_coarseGrainingL2FluxDefectBound_zero_forcing]

/--
Homogeneous coarse-graining corollary for an already packaged comparison pair.

This proof deliberately specializes the Section 3.3.B coarse-graining theorem
with depth zero and zero forcing, matching the manuscript proof of
Corollary `c.general.coarse.graining.homogeneous.deterministic.theory`.
-/
theorem solution_l2_close_harmonic_of_homogeneous_coarseFluxDefect_le_of_comparisonPair
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison :
      IsHomogenizationComparisonPairOn (cubeSet Q) a a0 u.toH1.grad v.toH1.grad)
    (hcoarseFluxDefect :
      harmonicApproximationFluxDefectBound Q a a0 s u ≤
        homogeneousCoarseGrainingFluxDefectBound Q a a0 s u) :
        solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
          homogeneousCoarseGrainingRhs Cdual Q a a0 s u := by
  have _ : IsEllipticMatrix lam0 Lam0 a0 := ha0
  have _ : a0.IsSymm := ha0symm
  have hcoarseFluxDefect' :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a a0 u.toH1.grad) 0 ≤
        coarseGrainingL2FluxDefectBound Q a a0 s 0 u.toH1.grad (0 : Vec d → Vec d) := by
    rw [← homogeneousCoarseGrainingFluxDefectBound_eq_coarseGrainingL2FluxDefectBound_zero_forcing]
    simpa [harmonicApproximationFluxDefectBound] using hcoarseFluxDefect
  calc
    solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad
        ≤ coarseGrainingL2Rhs Cdual Q a a0 s 0 u.toH1.grad (0 : Vec d → Vec d) :=
      solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le
        hdual Q a a0 sigma0 u.toH1.grad v.toH1.grad (0 : Vec d → Vec d) 0
        hsigma0 ha0eq hs_pos hs_lt_one hEll hcomparison hcoarseFluxDefect'
    _ = homogeneousCoarseGrainingRhs Cdual Q a a0 s u := by
      rw [← homogeneousCoarseGrainingRhs_eq_coarseGrainingL2Rhs_zero_forcing]

/--
Homogeneous coarse-graining corollary for
`coarsegraining/chapters/ch3_deterministic_theory.tex`, lines 3264--3292.

The single hypothesis `hcoarseFluxDefect` is the homogeneous local
flux-defect estimate.  When supplied by the coarse-graining side, this recovers
the displayed estimate for the `a₀`-harmonic replacement.  The boundary input
is the manuscript zero-trace condition for the replacement.
-/
theorem solution_l2_close_harmonic_of_homogeneous_coarseFluxDefect_le
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u : AHarmonicFunction a (cubeSet Q))
    (v : AHarmonicFunction (constantCoeffField a0) (cubeSet Q))
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.toH1.grad x - v.toH1.grad x))
    (hcoarseFluxDefect :
      harmonicApproximationFluxDefectBound Q a a0 s u ≤
        homogeneousCoarseGrainingFluxDefectBound Q a a0 s u) :
      solutionComparisonNegativeBesovLhs Q s a a0 u.toH1.grad v.toH1.grad ≤
        homogeneousCoarseGrainingRhs Cdual Q a a0 s u := by
  have hcoarseFluxDefectH1 :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 u.toH1.grad) 0 ≤
        homogeneousCoarseGrainingFluxDefectBoundH1 Q a a0 s u.toH1 := by
    simpa [harmonicApproximationFluxDefectBound, homogeneousCoarseGrainingFluxDefectBound]
      using hcoarseFluxDefect
  have hH1 :=
    solution_diff_l2_le_homogeneousCoarseGrainingRhsH1_of_zeroRhs_of_coarseFluxDefect_le
      hdual Q a a0 sigma0 u.toH1 v.toH1 hs_pos hs_lt_one hsigma0 ha0eq hEll ha0 ha0symm
      (IsH1DirichletRhsWeakSolutionOn.of_aHarmonicFunction u)
      (IsH1DirichletRhsWeakSolutionOn.of_aHarmonicFunction v)
      hzeroTrace hcoarseFluxDefectH1
  simpa [homogeneousCoarseGrainingRhs] using! hH1

end

end Homogenization
