/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.CoarseGrainingL2
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.NoteConstants

/-! # Coarse Graining L2Response -/

namespace Homogenization

noncomputable section

open scoped BigOperators ENNReal

/--
At depth zero, the one-cube §3.2.4 RHS flux-response bound is exactly the
flux-defect bound used by the Section 3.3.B coarse-graining wrapper.
-/
theorem coarseFluxResponseRHSBound_eq_coarseGrainingL2FluxDefectBound_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d) :
    coarseFluxResponseRHSBound Q a a0 s gradU g =
      coarseGrainingL2FluxDefectBound Q a a0 s 0 gradU g := by
  simp [coarseFluxResponseRHSBound, coarseGrainingL2FluxDefectBound]

/--
Depth-zero scalar comparison for the localized §3.2.4 RHS average.  The
nonnegativity hypothesis is exactly the `sqrt (B^2) = B` side condition.
-/
theorem localizedCoarseFluxResponseRHSBound_eq_coarseGrainingL2FluxDefectBound_zero_of_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (hbound_nonneg : 0 ≤ coarseFluxResponseRHSBound Q a a0 s gradU g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s 0 gradU g =
      coarseGrainingL2FluxDefectBound Q a a0 s 0 gradU g := by
  rw [localizedCoarseFluxResponseRHSBound_zero_of_nonneg Q a a0 s gradU g hbound_nonneg,
    coarseFluxResponseRHSBound_eq_coarseGrainingL2FluxDefectBound_zero]

/--
Depth-zero scalar comparison with the standard positive-Besov boundedness
input for the forcing term.
-/
theorem localizedCoarseFluxResponseRHSBound_eq_coarseGrainingL2FluxDefectBound_zero_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    localizedCoarseFluxResponseRHSBound Q a a0 s 0 gradU g =
      coarseGrainingL2FluxDefectBound Q a a0 s 0 gradU g :=
  localizedCoarseFluxResponseRHSBound_eq_coarseGrainingL2FluxDefectBound_zero_of_nonneg
    Q a a0 s gradU g
    (coarseFluxResponseRHSBound_nonneg_of_bddAbove Q a a0 gradU g hs hgBdd)

/-- The energy term in the Section 3.3.B flux-defect RHS is nonnegative. -/
theorem coarseGrainingL2FluxDefectEnergyTerm_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU : Vec d → Vec d) (hs : 0 < s) :
    0 ≤ coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU := by
  have hs_inv_nonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have herror_nonneg :
      0 ≤ coarseGrainingHomogenizationErrorAtDepth Q a a0 s j :=
    coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 j hs.le
  unfold coarseGrainingL2FluxDefectEnergyTerm
  exact
    mul_nonneg
      (mul_nonneg
        (mul_nonneg hs_inv_nonneg (Real.sqrt_nonneg _))
        herror_nonneg)
      (Real.sqrt_nonneg _)

/-- The full Section 3.3.B flux-defect RHS is nonnegative. -/
theorem coarseGrainingL2FluxDefectBound_nonneg_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    0 ≤ coarseGrainingL2FluxDefectBound Q a a0 s j gradU g := by
  rw [coarseGrainingL2FluxDefectBound_eq_energyTerm_add_forcingTerm]
  exact add_nonneg
    (coarseGrainingL2FluxDefectEnergyTerm_nonneg Q a a0 j gradU hs)
    (coarseGrainingL2FluxDefectForcingTerm_nonneg_of_bddAbove
      Q a a0 j g hs hgBdd)

/--
General coarse-graining comparison where the localized flux-defect hypothesis
is derived from descendant coarse-flux response data.

The remaining scalar input `hresponseBound` is the localization/Minkowski step
that compares the descendant response average with the manuscript RHS
`coarseGrainingL2FluxDefectBound`.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponse
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) (energy : Vec d → ℝ) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, 0 ≤ energy x)
    (henergy_int :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume)
    (hresp :
      ∀ R ∈ descendantsAtDepth Q j,
        CubeAverageFluxResponseControl R a a0 (fluxDefect a a0 gradU) energy)
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N (fluxDefect a a0 gradU)))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0))
    (hresponseBound :
      localizedCoarseFluxResponseAverageBound Q a a0 s j energy ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g := by
  have _ : IsEllipticMatrix lam0 Lam0 a0 := ha0
  have _ : a0.IsSymm := ha0symm
  have hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
    (localizedFluxDefectNegativeBesovAverageTwo_le_localizedCoarseFluxResponseAverageBound_of_descendant_coarseFluxResponse
      Q a a0 s (fluxDefect a a0 gradU) energy j hs_pos henergy_nonneg
      henergy_int hresp hpartialBdd hsum).trans hresponseBound
  exact
    solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le
      hdual Q a a0 sigma0 gradU gradV g j hsigma0 ha0eq hs_pos hs_lt_one hEll
      hcomparison
      hcoarseFluxDefect

/--
Same-right-hand-side coarse-graining wrapper with the local flux-defect bound
derived from descendant coarse-flux response data instead of supplied as
`hcoarseFluxDefect`.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_of_descendant_coarseFluxResponse
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d)
    (energy : Vec d → ℝ) {s : ℝ} (j : ℕ) {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R, 0 ≤ energy x)
    (henergy_int :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn energy (cubeSet R) MeasureTheory.volume)
    (hresp :
      ∀ R ∈ descendantsAtDepth Q j,
        CubeAverageFluxResponseControl R a a0 (fluxDefect a a0 u.grad) energy)
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N (fluxDefect a a0 u.grad)))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0))
    (hresponseBound :
      localizedCoarseFluxResponseAverageBound Q a a0 s j energy ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j u.grad g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponse
    hdual Q a a0 sigma0 u.grad v.grad g energy j hs_pos hs_lt_one hsigma0 ha0eq
    hEll ha0 ha0symm
    (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
      hEll ha0 u v g hu hv hzeroTrace)
    henergy_nonneg henergy_int hresp hpartialBdd hsum hresponseBound

/--
General coarse-graining comparison where the localized flux-defect hypothesis
is derived from descendant one-cube §3.2.4 RHS flux-response bounds.

The remaining scalar input `hresponseBound` is exactly the comparison between
the descendant `ℓ²` average of the §3.2.4 RHS and the manuscript §3.3.B
`coarseGrainingL2FluxDefectBound`.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hresponseBound :
      localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g := by
  have _ : IsEllipticMatrix lam0 Lam0 a0 := ha0
  have _ : a0.IsSymm := ha0symm
  have hlocalized :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j ≤
        localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g :=
    localizedFluxDefectNegativeBesovAverageTwo_fluxDefect_le_localizedCoarseFluxResponseRHSBound_of_descendant_bounds
      Q a a0 s gradU g j hdefect_bdd hRhs
  have hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s (fluxDefect a a0 gradU) j ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
    hlocalized.trans hresponseBound
  exact
    solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxDefect_le
      hdual Q a a0 sigma0 gradU gradV g j hsigma0 ha0eq hs_pos hs_lt_one hEll
      hcomparison
      hcoarseFluxDefect

/--
Same-right-hand-side version of
`solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound`.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_of_descendant_coarseFluxResponseRHSBound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d)
    {s : ℝ} (j : ℕ) {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 u.grad)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 u.grad) ≤
          coarseFluxResponseRHSBound R a a0 s u.grad g)
    (hresponseBound :
      localizedCoarseFluxResponseRHSBound Q a a0 s j u.grad g ≤
        coarseGrainingL2FluxDefectBound Q a a0 s j u.grad g) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j u.grad g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound
    hdual Q a a0 sigma0 u.grad v.grad g j hs_pos hs_lt_one hsigma0 ha0eq hEll
    ha0 ha0symm
    (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
      hEll ha0 u v g hu hv hzeroTrace)
    hdefect_bdd hRhs hresponseBound

/--
Pointwise component envelope for the scalar comparison between a one-cube
§3.2.4 RHS and the parent §3.3.B flux-defect RHS.

The remaining analytic scalar work is exactly the two hypotheses below:
localize the energy component into the parent energy term, and localize the
three correction components into the parent forcing term.
-/
theorem coarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_bounds
    {d : ℕ} (Q R : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d)
    (henergy :
      coarseFluxResponseRHSEnergyBound R a a0 s gradU ≤
        coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      coarseFluxResponseRHSResponseCorrectionBound R a a0 s g +
          coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
          coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
        coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    coarseFluxResponseRHSBound R a a0 s gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g := by
  rw [coarseFluxResponseRHSBound_eq_component_sum,
    coarseGrainingL2FluxDefectBound_eq_energyTerm_add_forcingTerm]
  simpa [add_assoc] using add_le_add henergy hforcing

/--
Scalar §3.3 RHS comparison from a pointwise descendant scalar envelope.
This converts the remaining `L²` descendant-average comparison into the
componentwise task of bounding every one-cube §3.2.4 RHS by the parent
`coarseGrainingL2FluxDefectBound`.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d)
    (hcoarse_nonneg :
      0 ≤ coarseGrainingL2FluxDefectBound Q a a0 s j gradU g)
    (hbound_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSBound R a a0 s gradU g)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSBound R a a0 s gradU g ≤
          coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
  localizedCoarseFluxResponseRHSBound_le_of_descendant_bound Q a a0 s j gradU g
    hcoarse_nonneg hbound_nonneg hpoint

/--
Bounded-positive-Besov version of the pointwise descendant scalar-envelope
comparison.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_bound_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d)
    (hs : 0 < s)
    (hcoarse_nonneg :
      0 ≤ coarseGrainingL2FluxDefectBound Q a a0 s j gradU g)
    (hgBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSBound R a a0 s gradU g ≤
          coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
  localizedCoarseFluxResponseRHSBound_le_of_descendant_bound_of_bddAbove
    Q a a0 j gradU g hs hcoarse_nonneg hgBdd hpoint

/--
Localized scalar §3.3 RHS comparison from descendant component envelopes.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (j : ℕ) (gradU g : Vec d → Vec d)
    (hcoarse_nonneg :
      0 ≤ coarseGrainingL2FluxDefectBound Q a a0 s j gradU g)
    (hbound_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSBound R a a0 s gradU g)
    (henergy :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSEnergyBound R a a0 s gradU ≤
          coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g +
            coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
            coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
  localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_bound
    Q a a0 s j gradU g hcoarse_nonneg hbound_nonneg
    (fun R hR =>
      coarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_bounds
        Q R a a0 s j gradU g (henergy R hR) (hforcing R hR))

/--
Bounded-positive-Besov version of the descendant component-envelope scalar
comparison.
-/
theorem localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_component_bounds_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (j : ℕ) (gradU g : Vec d → Vec d)
    (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (henergy :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSEnergyBound R a a0 s gradU ≤
          coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g +
            coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
            coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    localizedCoarseFluxResponseRHSBound Q a a0 s j gradU g ≤
      coarseGrainingL2FluxDefectBound Q a a0 s j gradU g :=
  localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_component_bounds
    Q a a0 s j gradU g
    (coarseGrainingL2FluxDefectBound_nonneg_of_bddAbove Q a a0 j gradU g hs hgBdd)
    (fun R hR =>
      coarseFluxResponseRHSBound_nonneg_of_bddAbove R a a0 gradU g hs
        (hgBdd_desc R hR))
    henergy hforcing

/--
§3.3 wrapper where the scalar RHS-average comparison is supplied in pointwise
descendant-envelope form.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_descendant_bound
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hcoarse_nonneg :
      0 ≤ coarseGrainingL2FluxDefectBound Q a a0 s j gradU g)
    (hbound_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSBound R a a0 s gradU g)
    (hpoint :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSBound R a a0 s gradU g ≤
          coarseGrainingL2FluxDefectBound Q a a0 s j gradU g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound
    hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hsigma0 ha0eq hEll
    ha0 ha0symm hcomparison
    hdefect_bdd hRhs
    (localizedCoarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_descendant_bound
      Q a a0 s j gradU g hcoarse_nonneg hbound_nonneg hpoint)

/--
§3.3 wrapper where the scalar RHS-average comparison is supplied by
descendant component envelopes.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_descendant_component_bounds
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hcoarse_nonneg :
      0 ≤ coarseGrainingL2FluxDefectBound Q a a0 s j gradU g)
    (hbound_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ coarseFluxResponseRHSBound R a a0 s gradU g)
    (henergy :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSEnergyBound R a a0 s gradU ≤
          coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g +
            coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
            coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_descendant_bound
    hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hsigma0 ha0eq hEll
    ha0 ha0symm hcomparison
    hdefect_bdd hRhs hcoarse_nonneg hbound_nonneg
    (fun R hR =>
      coarseFluxResponseRHSBound_le_coarseGrainingL2FluxDefectBound_of_component_bounds
        Q R a a0 s j gradU g (henergy R hR) (hforcing R hR))

/--
Bounded-positive-Besov version of the descendant component-envelope §3.3
wrapper.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_descendant_component_bounds_of_bddAbove
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)))
    (hRhs :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgBdd_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g))
    (henergy :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSEnergyBound R a a0 s gradU ≤
          coarseGrainingL2FluxDefectEnergyTerm Q a a0 s j gradU)
    (hforcing :
      ∀ R ∈ descendantsAtDepth Q j,
        coarseFluxResponseRHSResponseCorrectionBound R a a0 s g +
            coarseFluxResponseRHSWeakFluxCorrectionBound R a s g +
            coarseFluxResponseRHSPoincareCorrectionBound R a a0 s g ≤
          coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s j gradU g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound_of_descendant_component_bounds
    hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hsigma0 ha0eq hEll
    ha0 ha0symm hcomparison
    hdefect_bdd hRhs
    (coarseGrainingL2FluxDefectBound_nonneg_of_bddAbove Q a a0 j gradU g hs_pos hgBdd)
    (fun R hR =>
      coarseFluxResponseRHSBound_nonneg_of_bddAbove R a a0 gradU g hs_pos
        (hgBdd_desc R hR))
    henergy hforcing

/--
Depth-zero §3.3 wrapper through the one-cube §3.2.4 RHS flux-response bound.
At depth zero the scalar descendant-average comparison is closed internally.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxResponseRHSBound_zero
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ}
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (hdefect_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 gradU)))
    (hRhs :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
        coarseFluxResponseRHSBound Q a a0 s gradU g)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      coarseGrainingL2Rhs Cdual Q a a0 s 0 gradU g := by
  have hdefect_bdd_desc :
      ∀ R ∈ descendantsAtDepth Q 0,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N
            (fluxDefect a a0 gradU)) := by
    intro R hR
    simp at hR
    subst R
    exact hdefect_bdd
  have hRhs_desc :
      ∀ R ∈ descendantsAtDepth Q 0,
        cubeBesovNegativeVectorSeminormTwo R s (fluxDefect a a0 gradU) ≤
          coarseFluxResponseRHSBound R a a0 s gradU g := by
    intro R hR
    simp at hR
    subst R
    exact hRhs
  have hresponseBound :
      localizedCoarseFluxResponseRHSBound Q a a0 s 0 gradU g ≤
        coarseGrainingL2FluxDefectBound Q a a0 s 0 gradU g := by
    exact le_of_eq
      (localizedCoarseFluxResponseRHSBound_eq_coarseGrainingL2FluxDefectBound_zero_of_bddAbove
        Q a a0 gradU g hs_pos hgBdd)
  exact
    solution_diff_l2_le_coarseGrainingL2Rhs_of_descendant_coarseFluxResponseRHSBound
      hdual Q a a0 sigma0 gradU gradV g 0 hs_pos hs_lt_one hsigma0 ha0eq hEll
      ha0 ha0symm hcomparison
      hdefect_bdd_desc hRhs_desc hresponseBound

/--
Same-right-hand-side depth-zero wrapper through the one-cube §3.2.4 RHS
flux-response bound.
-/
theorem solution_diff_l2_le_coarseGrainingL2Rhs_of_sameRhs_of_coarseFluxResponseRHSBound_zero
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (u v : H1Function (cubeSet Q)) (g : Vec d → Vec d)
    {s : ℝ} {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hu : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) u g)
    (hv : IsH1DirichletRhsWeakSolutionOn (constantCoeffField a0) (cubeSet Q) v g)
    (hzeroTrace :
      IsPotentialZeroTraceOn (cubeSet Q) (fun x => u.grad x - v.grad x))
    (hdefect_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 u.grad)))
    (hRhs :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 u.grad) ≤
        coarseFluxResponseRHSBound Q a a0 s u.grad g)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    solutionComparisonNegativeBesovLhs Q s a a0 u.grad v.grad ≤
      coarseGrainingL2Rhs Cdual Q a a0 s 0 u.grad g :=
  solution_diff_l2_le_coarseGrainingL2Rhs_of_coarseFluxResponseRHSBound_zero
    hdual Q a a0 sigma0 u.grad v.grad g hs_pos hs_lt_one hsigma0 ha0eq hEll
    ha0 ha0symm
    (IsHomogenizationComparisonPairOn.of_sameRhs_h1Functions
      hEll ha0 u v g hu hv hzeroTrace)
    hdefect_bdd hRhs hgBdd

/--
General coarse-graining comparison where the localized flux-defect hypothesis
is derived from descendant coarse-flux response data and the scalar response
average is absorbed into the Section 3.3.B RHS with the explicit ten-factor
constant.

The assumptions `hgeom_le`, `herror_nonneg`, and `hforcing_nonneg` are the
remaining scalar side conditions needed to keep this wrapper import-light:
the note-constant file supplies `hgeom_le`, while later positivity wrappers can
close the two nonnegativity inputs.
-/
theorem solution_diff_l2_le_ten_mul_coarseGrainingL2Rhs_of_descendant_coarseFluxResponse_energy
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hgeom_le : (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (hresp :
      ∀ R ∈ descendantsAtDepth Q j,
        CubeAverageFluxResponseControl R a a0 (fluxDefect a a0 gradU)
          (coefficientEnergyDensity a gradU))
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N (fluxDefect a a0 gradU)))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0))
    (herror_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0)
    (hforcing_nonneg :
      0 ≤ coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      10 * coarseGrainingL2Rhs Cdual Q a a0 s j gradU g := by
  subst a0
  have henergy_nonneg :
      ∀ R ∈ descendantsAtDepth Q j, ∀ x ∈ cubeSet R,
        0 ≤ coefficientEnergyDensity a gradU x := by
    intro R hR x hx
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll gradU x
      (cubeSet_subset_of_mem_descendantsAtDepth hR hx)
  have henergy_avg_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ cubeAverage R (coefficientEnergyDensity a gradU) := by
    intro R hR
    exact cubeAverage_nonneg_of_nonneg_on
      (Q := R) (f := coefficientEnergyDensity a gradU) (henergy_nonneg R hR)
  have henergy_int_desc :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
          (cubeSet R) MeasureTheory.volume := by
    intro R hR
    exact henergy_int.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hlocalized_response :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j ≤
        localizedCoarseFluxResponseAverageBound Q a
          (scalarMatrix (d := d) sigma0) s j
          (coefficientEnergyDensity a gradU) :=
    localizedFluxDefectNegativeBesovAverageTwo_le_localizedCoarseFluxResponseAverageBound_of_descendant_coarseFluxResponse
      Q a (scalarMatrix (d := d) sigma0) s
      (fluxDefect a (scalarMatrix (d := d) sigma0) gradU)
      (coefficientEnergyDensity a gradU) j
      hs_pos henergy_nonneg henergy_int_desc hresp hpartialBdd hsum
  have hresponse_bound :
      localizedCoarseFluxResponseAverageBound Q a
          (scalarMatrix (d := d) sigma0) s j
          (coefficientEnergyDensity a gradU) ≤
        10 * coarseGrainingL2FluxDefectBound Q a
          (scalarMatrix (d := d) sigma0) s j gradU g :=
    localizedCoarseFluxResponseAverageBound_coefficientEnergy_le_ten_mul_coarseGrainingL2FluxDefectBound_of_invGeom_le
      Q a (scalarMatrix (d := d) sigma0) j gradU g hs_pos hgeom_le henergy_int
      henergy_avg_nonneg
      herror_nonneg hforcing_nonneg
  have hcoarseFluxDefect :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j ≤
        10 * coarseGrainingL2FluxDefectBound Q a
          (scalarMatrix (d := d) sigma0) s j gradU g :=
    hlocalized_response.trans hresponse_bound
  calc
    solutionComparisonNegativeBesovLhs Q s a (scalarMatrix (d := d) sigma0) gradU gradV
        ≤ Cdual * s⁻¹ *
      localizedFluxDefectNegativeBesovAverageTwo Q s
        (fluxDefect a (scalarMatrix (d := d) sigma0) gradU) j :=
      solution_diff_l2_le_dualityConstant_mul_localizedFluxDefect_of_fluxDefect_negativeBesov_le
        hdual Q a sigma0 gradU gradV j hsigma0 hs_pos hs_lt_one hEll hcomparison
    _ ≤ Cdual * s⁻¹ *
          (10 * coarseGrainingL2FluxDefectBound Q a
            (scalarMatrix (d := d) sigma0) s j gradU g) := by
        exact mul_le_mul_of_nonneg_left hcoarseFluxDefect
          (mul_nonneg hdual.1 (inv_nonneg.mpr hs_pos.le))
    _ = 10 * coarseGrainingL2Rhs Cdual Q a
          (scalarMatrix (d := d) sigma0) s j gradU g := by
        unfold coarseGrainingL2Rhs
        ring

/--
Import-light side conditions in the response-data apex discharged from the
standard manuscript range and the global positive-Besov boundedness of `g`.
-/
theorem solution_diff_l2_le_ten_mul_coarseGrainingL2Rhs_of_descendant_coarseFluxResponse_energy_of_bddAbove
    {d : ℕ} [NeZero d] {Cdual : ℝ}
    (hdual : ScalarSolutionComparisonDualityEstimate d Cdual)
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (sigma0 : ℝ)
    (gradU gradV g : Vec d → Vec d) {s : ℝ} (j : ℕ)
    {lam Lam lam0 Lam0 : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hsigma0 : 0 < sigma0)
    (ha0eq : a0 = scalarMatrix (d := d) sigma0)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (ha0symm : a0.IsSymm)
    (hcomparison : IsHomogenizationComparisonPairOn (cubeSet Q) a a0 gradU gradV)
    (henergy_int :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a gradU)
        (cubeSet Q) MeasureTheory.volume)
    (hresp :
      ∀ R ∈ descendantsAtDepth Q j,
        CubeAverageFluxResponseControl R a a0 (fluxDefect a a0 gradU)
          (coefficientEnergyDensity a gradU))
    (hpartialBdd :
      ∀ R ∈ descendantsAtDepth Q j,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminorm R s N (fluxDefect a a0 gradU)))
    (hsum :
      ∀ R ∈ descendantsAtDepth Q j,
        Summable (fun n : ℕ =>
          geometricWeight s 1 n *
            scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity a a0))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    solutionComparisonNegativeBesovLhs Q s a a0 gradU gradV ≤
      10 * coarseGrainingL2Rhs Cdual Q a a0 s j gradU g := by
  have hgeom_le : (geometricDiscount s 1)⁻¹ ≤ 5 * s⁻¹ := by
    simpa [geometricDiscount_one_eq] using
      inv_one_sub_rpow_three_neg_le_five_inv hs_pos hs_lt_one.le
  have herror_nonneg :
      ∀ R ∈ descendantsAtDepth Q j,
        0 ≤ HomogenizationErrorOnCube R s .infinity (.finite 1) a a0 := by
    intro R hR
    exact homogenizationErrorOnCube_infinity_one_nonneg R a a0 hs_pos.le
  have hforcing_nonneg :
      0 ≤ coarseGrainingL2FluxDefectForcingTerm Q a a0 s j g :=
    coarseGrainingL2FluxDefectForcingTerm_nonneg_of_bddAbove
      Q a a0 j g hs_pos hgBdd
  exact
    solution_diff_l2_le_ten_mul_coarseGrainingL2Rhs_of_descendant_coarseFluxResponse_energy
      hdual Q a a0 sigma0 gradU gradV g j hs_pos hs_lt_one hgeom_le hsigma0
      ha0eq hEll ha0 ha0symm hcomparison henergy_int hresp hpartialBdd hsum herror_nonneg
      hforcing_nonneg

end

end Homogenization
