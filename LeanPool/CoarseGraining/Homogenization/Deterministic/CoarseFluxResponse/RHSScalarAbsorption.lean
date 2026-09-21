/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSCorrections

/-! # RHSScalar Absorption -/

namespace Homogenization

noncomputable section

/-!
# Scalar absorption for the RHS coarse-flux response

This leaf module keeps the scalar bookkeeping for manuscript §3.2.4 out of the
main split/recomposition files.  The estimates here turn the expanded
§3.2.3/Poincare square-root RHSs into compact correction components once the
corresponding square-side adequacy inequalities are supplied, and absorb the
`sqrt 2` triangle constants into a dimension-constant envelope.
-/

open scoped BigOperators ENNReal

private theorem sqrt_two_mul_add_le_two_mul_add {A B : ℝ}
    (hB : 0 ≤ B) :
    Real.sqrt 2 * (Real.sqrt 2 * A + B) ≤ 2 * (A + B) := by
  have hsqrt_two_sq : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hsqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
    have hlt : Real.sqrt 2 < (3 / 2 : ℝ) := Real.sqrt_two_lt_three_halves
    linarith
  calc
    Real.sqrt 2 * (Real.sqrt 2 * A + B)
        = (Real.sqrt 2 * Real.sqrt 2) * A + Real.sqrt 2 * B := by
          ring
    _ = 2 * A + Real.sqrt 2 * B := by
          rw [hsqrt_two_sq]
    _ ≤ 2 * A + 2 * B := by
          exact add_le_add (le_refl (2 * A))
            (mul_le_mul_of_nonneg_right hsqrt_two_le_two hB)
    _ = 2 * (A + B) := by ring

/-- The square radicand in the expanded weak-flux correction bound. -/
noncomputable def coarseFluxResponseRHSWeakFluxExpandedRadicand {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) (m : ℕ) (BU BV : ℝ) : ℝ :=
  (coarsePoincareRHSDepthWeight s m)⁻¹ *
    (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        cubeAverage Q (coefficientEnergyDensity a gradV) +
      (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

/-- The expanded weak-flux correction bound is the square root of its radicand. -/
theorem coarseFluxResponseRHSWeakFluxExpandedBound_eq_sqrt_radicand {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) (m : ℕ) (BU BV : ℝ) :
    coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV m BU BV =
      Real.sqrt
        (coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g gradV m BU BV) := by
  rfl

/-- Nonnegativity of the expanded weak-flux correction radicand. -/
theorem coarseFluxResponseRHSWeakFluxExpandedRadicand_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g gradV : Vec d → Vec d) (m : ℕ) {BU BV : ℝ}
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV) :
    0 ≤ coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g gradV m BU BV := by
  have hweight_nonneg : 0 ≤ (coarsePoincareRHSDepthWeight s m)⁻¹ := by
    refine inv_nonneg.mpr ?_
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hLambda_nonneg :
      0 ≤ LambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * 2)
  have henergy_coeff_nonneg :
      0 ≤ 50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a := by
    positivity
  have htail_coeff_nonneg : 0 ≤ 5 * s⁻¹ := by
    positivity
  have hforce_nonneg :
      0 ≤
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    positivity
  unfold coarseFluxResponseRHSWeakFluxExpandedRadicand
  exact mul_nonneg hweight_nonneg
    (add_nonneg
      (add_nonneg
        (add_nonneg
          (mul_nonneg henergy_coeff_nonneg havg_nonneg)
          (mul_nonneg htail_coeff_nonneg hBU_nonneg))
        (mul_nonneg htail_coeff_nonneg hBV_nonneg))
      hforce_nonneg)

/--
Square-side scalar absorption for the weak-flux correction component.

The remaining analytic input is the radicand inequality, which is where the
zero-Dirichlet energy estimate for the correction field is inserted.
-/
theorem coarseFluxResponseRHSWeakFluxExpandedBound_le_correctionBound_of_radicand_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g gradV : Vec d → Vec d) (m : ℕ) {BU BV : ℝ}
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hrad :
      coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g gradV m BU BV ≤
        (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV m BU BV ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  rw [coarseFluxResponseRHSWeakFluxExpandedBound_eq_sqrt_radicand]
  exact Real.sqrt_le_of_le_sq
    (coarseFluxResponseRHSWeakFluxExpandedRadicand_nonneg
      Q a g gradV m hs havg_nonneg hBU_nonneg hBV_nonneg)
    (coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
      Q a g hs hgBdd)
    hrad

/--
Depth-zero weak-flux radicand absorption from four component budgets.

This is the scalar bookkeeping form of the remaining manuscript estimate: the
energy, two tail terms, and forcing term may be proved separately and then
summed into the compact correction square.
-/
theorem coarseFluxResponseRHSWeakFluxExpandedRadicand_zero_le_correctionBound_sq_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) {BU BV Benergy BUtail BVtail Bforce : ℝ}
    (henergy :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        Benergy)
    (hBU : (5 * s⁻¹) * BU ≤ BUtail)
    (hBV : (5 * s⁻¹) * BV ≤ BVtail)
    (hforce :
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        Bforce)
    (hsum :
      Benergy + BUtail + BVtail + Bforce ≤
        (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g gradV 0 BU BV ≤
      (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2 := by
  unfold coarseFluxResponseRHSWeakFluxExpandedRadicand
  simp only [coarsePoincareRHSDepthWeight_zero, inv_one, one_mul]
  nlinarith [henergy, hBU, hBV, hforce, hsum]

/--
Weak-flux square-root absorption from component budgets and the standard
nonnegativity/boundedness hypotheses.
-/
theorem coarseFluxResponseRHSWeakFluxExpandedBound_le_correctionBound_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g gradV : Vec d → Vec d) {BU BV Benergy BUtail BVtail Bforce : ℝ}
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (henergy :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        Benergy)
    (hBU : (5 * s⁻¹) * BU ≤ BUtail)
    (hBV : (5 * s⁻¹) * BV ≤ BVtail)
    (hforce :
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        Bforce)
    (hsum :
      Benergy + BUtail + BVtail + Bforce ≤
        (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  exact
    coarseFluxResponseRHSWeakFluxExpandedBound_le_correctionBound_of_radicand_le_sq
      Q a g gradV 0 hs havg_nonneg hBU_nonneg hBV_nonneg hgBdd
      (coarseFluxResponseRHSWeakFluxExpandedRadicand_zero_le_correctionBound_sq_of_component_bounds
        Q a s g gradV henergy hBU hBV hforce hsum)

/--
Depth-zero weak-flux component bridge with the scalar side supplied as
component budgets rather than one opaque expanded-RHS comparison.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_localized_depth_zero_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (gradV g : Vec d → Vec d) {BU BV Benergy BUtail BVtail Bforce : ℝ}
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (hlocalized :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (gradV x)) 0 ≤
        coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV)
    (henergy :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a gradV) ≤
        Benergy)
    (hBU : (5 * s⁻¹) * BU ≤ BUtail)
    (hBV : (5 * s⁻¹) * BV ≤ BVtail)
    (hforce :
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        Bforce)
    (hsum :
      Benergy + BUtail + BVtail + Bforce ≤
        (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_matVecMul_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_localized_depth_zero
      Q a s gradV g hfluxV_bdd hlocalized
      (coarseFluxResponseRHSWeakFluxExpandedBound_le_correctionBound_of_component_bounds
        Q a g gradV hs havg_nonneg hBU_nonneg hBV_nonneg hgBdd
        henergy hBU hBV hforce hsum)

/--
H¹ weak-solution weak-flux correction with the scalar side expressed as the
square-radicand inequality which remains after inserting the correction-field
energy estimate.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_expanded_radicand_le_sq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad)
    (hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
    (hsum_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun m : ℕ =>
          geometricWeight s 2 m *
            maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (v.grad x))))
    (huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N v.grad))
    (hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    {BU BV : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a v.grad)
        (cubeSet Q) MeasureTheory.volume)
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
    (hu_tail :
      ∀ k : ℕ, coarsePoincareRHSSn Q s v.grad k ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              v.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV)
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))))
    (hrad :
      coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g v.grad 0 BU BV ≤
        (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (v.grad x)) ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn
      Q a s g v hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed hfluxV_bdd
      (coarseFluxResponseRHSWeakFluxExpandedBound_le_correctionBound_of_radicand_le_sq
        Q a g v.grad 0 hs havg_parent_nonneg hBU_nonneg hBV_nonneg
        hGlobalBdd hrad)

/--
H¹ weak-solution weak-flux correction with the scalar side supplied as the
four component budgets of the expanded depth-zero radicand.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hEll_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hu_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) v.grad)
    (hg_mem_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        MemVectorL2 (cubeSet R) g)
    (hC_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        H1CoerciveEstimate (cubeSet R))
    (hData_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        OpenCubeDescendantDeterministicCoarseData R a)
    (hsum_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        Summable (fun m : ℕ =>
          geometricWeight s 2 m *
            maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a))
    (hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (v.grad x))))
    (huBdd_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovNegativeVectorPartialSeminormTwo R s N v.grad))
    (hgBdd_centered_desc :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N
            (fun x => g x - cubeAverageVec R g)))
    {BU BV Benergy BUtail BVtail Bforce : ℝ}
    (hBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s v.grad n))
    (hEll_open : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hsum_half :
      Summable (fun l : ℕ =>
        geometricWeight (s / 2) 2 l *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (l : ℤ)) a) 1))
    (havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad))
    (havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a v.grad)
        (cubeSet Q) MeasureTheory.volume)
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
    (hu_tail :
      ∀ k : ℕ, coarsePoincareRHSSn Q s v.grad k ≤ BU)
    (hvConstructed :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∀ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∀ w : AHarmonicFunction a (cubeSet R),
            (∀ x ∈ cubeSet R,
              v.grad x = w.toH1.grad x + ω.toH1MeanZero.toH1Function.grad x) →
            BddAbove (Set.range fun N : ℕ =>
              cubeBesovNegativeVectorPartialSeminormTwo R s N
                (fun x => w.toH1.grad x)) ∧
            (cubeBesovNegativeVectorSeminormTwo R s
              (fun x => w.toH1.grad x)) ^ 2 ≤
              (coarsePoincareRHSDepthWeight s j)⁻¹ * BV)
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (v.grad x))))
    (henergy :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) ≤
        Benergy)
    (hBU : (5 * s⁻¹) * BU ≤ BUtail)
    (hBV : (5 * s⁻¹) * BV ≤ BVtail)
    (hforce :
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        Bforce)
    (hbudget :
      Benergy + BUtail + BVtail + Bforce ≤
        (coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (v.grad x)) ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_expanded_radicand_le_sq
      Q a s g v hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc
      hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed hfluxV_bdd
      (coarseFluxResponseRHSWeakFluxExpandedRadicand_zero_le_correctionBound_sq_of_component_bounds
        Q a s g v.grad henergy hBU hBV hforce hbudget)

/-- The square radicand in the expanded RHS Poincare correction bound. -/
noncomputable def coarseFluxResponseRHSPoincareExpandedRadicand {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) : ℝ :=
  250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
      cubeAverage Q (coefficientEnergyDensity a gradV) +
    15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2

/-- The expanded RHS Poincare correction bound is the square root of its radicand. -/
theorem coarseFluxResponseRHSPoincareExpandedBound_eq_sqrt_radicand {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) :
    coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV =
      Real.sqrt
        (coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV) := by
  rfl

/-- Nonnegativity of the expanded RHS Poincare correction radicand. -/
theorem coarseFluxResponseRHSPoincareExpandedRadicand_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (g gradV : Vec d → Vec d)
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV)) :
    0 ≤ coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV := by
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * 2)
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have henergy_coeff_nonneg :
      0 ≤ 250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ := by
    positivity
  have hforce_nonneg :
      0 ≤
        15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    positivity
  unfold coarseFluxResponseRHSPoincareExpandedRadicand
  exact add_nonneg (mul_nonneg henergy_coeff_nonneg havg_nonneg) hforce_nonneg

/--
Square-side scalar absorption for the constant-coefficient Poincare correction.

This is shaped to discharge the `matNorm a0 * expanded ≤ compact` hypothesis in
`RHSCorrections` after proving the manuscript energy-to-force square bound.
-/
theorem matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_correctionBound_of_radicand_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {s : ℝ}
    (g gradV : Vec d → Vec d)
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hrad :
      (matNorm a0) ^ 2 *
          coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  have hrad_nonneg :
      0 ≤ coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV :=
    coarseFluxResponseRHSPoincareExpandedRadicand_nonneg Q a g gradV hs havg_nonneg
  have hleft_sq :
      (matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV) ^ 2 =
        (matNorm a0) ^ 2 *
          coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV := by
    rw [coarseFluxResponseRHSPoincareExpandedBound_eq_sqrt_radicand,
      mul_pow, Real.sq_sqrt hrad_nonneg]
  refine le_of_sq_le_sq ?_
    (coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
      Q a a0 g hs hgBdd)
  simpa [hleft_sq] using hrad

/--
Poincare radicand absorption from separate energy and forcing budgets after
multiplying by the constant-coefficient matrix norm.
-/
theorem matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_correctionBound_sq_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (s : ℝ)
    (g gradV : Vec d → Vec d) {Benergy Bforce : ℝ}
    (henergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a gradV)) ≤
        Benergy)
    (hforce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Bforce)
    (hsum :
      Benergy + Bforce ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    (matNorm a0) ^ 2 *
        coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV ≤
      (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  unfold coarseFluxResponseRHSPoincareExpandedRadicand
  nlinarith [henergy, hforce, hsum]

/--
Poincare square-root absorption from component budgets and the standard
nonnegativity/boundedness hypotheses.
-/
theorem matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_correctionBound_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {s : ℝ}
    (g gradV : Vec d → Vec d)
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    {Benergy Bforce : ℝ}
    (henergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a gradV)) ≤
        Benergy)
    (hforce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Bforce)
    (hsum :
      Benergy + Bforce ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  exact
    matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_correctionBound_of_radicand_le_sq
      Q a a0 g gradV hs havg_nonneg hgBdd
      (matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_correctionBound_sq_of_component_bounds
        Q a a0 s g gradV henergy hforce hsum)

/--
Poincare component bridge with the compact scalar correction supplied by
energy/forcing budgets.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound_and_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradV g : Vec d → Vec d) {Benergy Bforce : ℝ}
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hmat :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (gradV x)) ≤
        matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s gradV)
    (hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s gradV ≤
        coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV)
    (henergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a gradV)) ≤
        Benergy)
    (hforce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Bforce)
    (hsum :
      Benergy + Bforce ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound
      Q a a0 s gradV g hmat hgrad
      (matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_correctionBound_of_component_bounds
        Q a a0 g gradV hs havg_nonneg hgBdd henergy hforce hsum)

/--
Poincare component bridge with constant-matrix action discharged from
descendant `L²` data, and scalar correction supplied by component budgets.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound_and_descendant_mem_and_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradV g : Vec d → Vec d) {Benergy Bforce : ℝ}
    (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgrad_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) gradV)
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N gradV))
    (hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s gradV ≤
        coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV)
    (henergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a gradV)) ≤
        Benergy)
    (hforce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Bforce)
    (hsum :
      Benergy + Bforce ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound_and_descendant_mem
      Q a a0 s gradV g hgrad_mem_desc hgrad_bdd hgrad
      (matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_correctionBound_of_component_bounds
        Q a a0 g gradV hs havg_nonneg hgBdd henergy hforce hsum)

/--
H¹ weak-solution Poincare correction with the scalar side expressed as the
square-radicand inequality remaining after the correction-field energy bound.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_expanded_radicand_le_sq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgrad_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) v.grad)
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad))
    (hrad :
      (matNorm a0) ^ 2 *
          coarseFluxResponseRHSPoincareExpandedRadicand Q a s g v.grad ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (v.grad x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  have havg_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad) :=
    cubeAverage_nonneg_of_nonneg_on (Q := Q)
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll v.grad)
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn
      Q a a0 s g v hs hs_le hEll hweak hg hGlobalBdd
      hgrad_mem_desc hgrad_bdd
      (matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_correctionBound_of_radicand_le_sq
        Q a a0 g v.grad hs havg_nonneg hGlobalBdd hrad)

/--
H¹ weak-solution Poincare correction with the scalar side supplied as
matrix-weighted energy and forcing budgets.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    {lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgrad_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) v.grad)
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N v.grad))
    {Benergy Bforce : ℝ}
    (henergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) ≤
        Benergy)
    (hforce :
      (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        Bforce)
    (hbudget :
      Benergy + Bforce ≤
        (coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (v.grad x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_expanded_radicand_le_sq
      Q a a0 s g v hs hs_le hEll hweak hg hGlobalBdd
      hgrad_mem_desc hgrad_bdd
      (matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_correctionBound_sq_of_component_bounds
        Q a a0 s g v.grad henergy hforce hbudget)

/--
The split-envelope constants are absorbed into a single factor `2`.  This is
the local `C(d)` bookkeeping for the `sqrt 2` triangle inequalities.
-/
theorem coarseFluxResponseRHSSplitEnvelope_le_two_mul_coarseFluxResponseRHSBound_of_poincare_nonneg
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradU g : Vec d → Vec d)
    (hpoincare_nonneg : 0 ≤ coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    coarseFluxResponseRHSSplitEnvelope Q a a0 s gradU g ≤
      2 * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  let H : ℝ := coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g
  let W : ℝ := coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g
  let P : ℝ := coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g
  calc
    coarseFluxResponseRHSSplitEnvelope Q a a0 s gradU g
        = Real.sqrt 2 * (Real.sqrt 2 * (H + W) + P) := by
          simp [H, W, P, coarseFluxResponseRHSSplitEnvelope]
    _ ≤ 2 * ((H + W) + P) :=
          sqrt_two_mul_add_le_two_mul_add hpoincare_nonneg
    _ = 2 * coarseFluxResponseRHSBound Q a a0 s gradU g := by
          rw [coarseFluxResponseRHSBound_eq_component_sum]
          simp [H, W, P, coarseFluxResponseRHSHomogeneousSplitBound]

/-- Bounded-positive-Besov version of the split-envelope constant absorption. -/
theorem coarseFluxResponseRHSSplitEnvelope_le_two_mul_coarseFluxResponseRHSBound_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU g : Vec d → Vec d) (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    coarseFluxResponseRHSSplitEnvelope Q a a0 s gradU g ≤
      2 * coarseFluxResponseRHSBound Q a a0 s gradU g :=
  coarseFluxResponseRHSSplitEnvelope_le_two_mul_coarseFluxResponseRHSBound_of_poincare_nonneg
    Q a a0 s gradU g
    (coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove Q a a0 g hs hgBdd)

/--
Split-component RHS flux-response estimate with the triangle constants
absorbed into the factor `2`.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_coarseFluxResponseRHSBound_of_split_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {s : ℝ} (gradU gradW gradV g : Vec d → Vec d)
    (hs : 0 < s)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hgrad : ∀ x ∈ cubeSet Q, gradU x = gradW x + gradV x)
    (hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 gradW))
    (hfluxV_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (gradV x)))
    (ha0V_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (gradV x)))
    (hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 gradW)))
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (gradV x))))
    (hdefectW :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradW) ≤
        coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g)
    (hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g)
    (ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * coarseFluxResponseRHSBound Q a a0 s gradU g := by
  exact
    (cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseRHSSplitEnvelope_of_split_component_bounds
      Q a a0 s gradU gradW gradV g hgrad
      hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd hdefectW hfluxV ha0V).trans
      (coarseFluxResponseRHSSplitEnvelope_le_two_mul_coarseFluxResponseRHSBound_of_bddAbove
        Q a a0 gradU g hs hgBdd)

end

end Homogenization
