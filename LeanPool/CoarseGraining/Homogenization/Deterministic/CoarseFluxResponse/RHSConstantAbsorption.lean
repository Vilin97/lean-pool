/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSScalarAbsorption

/-! # RHSConstant Absorption -/

namespace Homogenization

noncomputable section

/-!
# Constant-envelope scalar absorption for the RHS coarse-flux response

The scalar absorption hooks in `RHSScalarAbsorption` target the bare correction
components.  The manuscript §3.2.4 theorem carries a dimensional constant, so
this leaf exposes the same hooks with a caller-supplied nonnegative multiplier.
-/

open scoped BigOperators ENNReal

/-- Weak-flux radicand component budgets closing into `C * correctionBound`. -/
theorem coarseFluxResponseRHSWeakFluxExpandedRadicand_zero_le_const_mul_correctionBound_sq_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (C s : ℝ)
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
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g gradV 0 BU BV ≤
      (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2 := by
  unfold coarseFluxResponseRHSWeakFluxExpandedRadicand
  simp only [coarsePoincareRHSDepthWeight_zero, inv_one, one_mul]
  nlinarith [henergy, hBU, hBV, hforce, hsum]

/-- Weak-flux square-root absorption into `C * correctionBound`. -/
theorem coarseFluxResponseRHSWeakFluxExpandedBound_le_const_mul_correctionBound_of_radicand_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {C s : ℝ}
    (g gradV : Vec d → Vec d) (m : ℕ) {BU BV : ℝ}
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hrad :
      coarseFluxResponseRHSWeakFluxExpandedRadicand Q a s g gradV m BU BV ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV m BU BV ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  rw [coarseFluxResponseRHSWeakFluxExpandedBound_eq_sqrt_radicand]
  exact Real.sqrt_le_of_le_sq
    (coarseFluxResponseRHSWeakFluxExpandedRadicand_nonneg
      Q a g gradV m hs havg_nonneg hBU_nonneg hBV_nonneg)
    (mul_nonneg hC_nonneg
      (coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
        Q a g hs hgBdd))
    hrad

/-- Weak-flux square-root absorption into `C * correctionBound` from budgets. -/
theorem coarseFluxResponseRHSWeakFluxExpandedBound_le_const_mul_correctionBound_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {C s : ℝ}
    (g gradV : Vec d → Vec d) {BU BV Benergy BUtail BVtail Bforce : ℝ}
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
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
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
  coarseFluxResponseRHSWeakFluxExpandedBound_le_const_mul_correctionBound_of_radicand_le_sq
    Q a g gradV 0 hC_nonneg hs havg_nonneg hBU_nonneg hBV_nonneg hgBdd
    (coarseFluxResponseRHSWeakFluxExpandedRadicand_zero_le_const_mul_correctionBound_sq_of_component_bounds
      Q a C s g gradV henergy hBU hBV hforce hsum)

/--
Weak-flux square-root absorption with the scalar side stated as the exact
expanded depth-zero budget.
-/
theorem coarseFluxResponseRHSWeakFluxExpandedBound_le_const_mul_correctionBound_of_exact_budget
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {C s : ℝ}
    (g gradV : Vec d → Vec d) {BU BV : ℝ}
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hbudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a gradV) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
  coarseFluxResponseRHSWeakFluxExpandedBound_le_const_mul_correctionBound_of_component_bounds
    (Q := Q) (a := a) (g := g) (gradV := gradV)
    (C := C) (s := s) (BU := BU) (BV := BV)
    (Benergy :=
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        cubeAverage Q (coefficientEnergyDensity a gradV))
    (BUtail := (5 * s⁻¹) * BU)
    (BVtail := (5 * s⁻¹) * BV)
    (Bforce :=
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
    hC_nonneg hs havg_nonneg hBU_nonneg hBV_nonneg hgBdd
    (by rfl) (by rfl) (by rfl) (by rfl) hbudget

/-- Depth-zero weak-flux local handoff to an arbitrary scalar envelope. -/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_le_of_localized_depth_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (gradV g : Vec d → Vec d) {BU BV B : ℝ}
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (hlocalized :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (gradV x)) 0 ≤
        coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV)
    (hscalar :
      coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV ≤ B) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤ B := by
  have hnonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s
      (fun x => matVecMul (a x) (gradV x)) hfluxV_bdd
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x))
        =
      localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (gradV x)) 0 := by
          exact
            (localizedFluxDefectNegativeBesovAverageTwo_depth_zero_of_nonneg
              Q s (fun x => matVecMul (a x) (gradV x)) hnonneg).symm
    _ ≤ coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV :=
          hlocalized
    _ ≤ B := hscalar

/--
H¹ weak-solution weak-flux correction with the scalar side supplied as
component budgets closing into a caller-supplied multiple of the compact bound.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    (C : ℝ) {lam Lam : ℝ}
    (hCmul_nonneg : 0 ≤ C)
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
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (v.grad x)) ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  have hlocalized :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (v.grad x)) 0 ≤
        coarseFluxResponseRHSWeakFluxExpandedBound Q a s g v.grad 0 BU BV := by
    simpa [coarseFluxResponseRHSWeakFluxExpandedBound] using
      localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_noteEnergySeminormsForce_of_h1DirichletRhsWeakSolutionOn_of_constructed_harmonicRemainder_bounds
        (Q := Q) (a := a) (s := s) (g := g) (u := v) (lam := lam)
        (Lam := Lam) hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc
        hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
        hgBdd_centered_desc (m := 0) (BU := BU) (BV := BV) hBdd
        hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint
        hmem hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg
        (by intro k; simpa using hu_tail k) hvConstructed
  exact
    cubeBesovNegativeVectorSeminormTwo_matVecMul_le_of_localized_depth_zero
      Q a s v.grad g hfluxV_bdd hlocalized
      (coarseFluxResponseRHSWeakFluxExpandedBound_le_const_mul_correctionBound_of_component_bounds
        Q a g v.grad hCmul_nonneg hs havg_parent_nonneg hBU_nonneg hBV_nonneg
        hGlobalBdd henergy hBU hBV hforce hbudget)

/--
H¹ weak-solution weak-flux correction with the scalar side stated as the exact
expanded depth-zero budget.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_exact_budget
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    (C : ℝ) {lam Lam : ℝ}
    (hCmul_nonneg : 0 ≤ C)
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
    (hbudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (v.grad x)) ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
  cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
    (Q := Q) (a := a) (s := s) (g := g) (v := v) (C := C)
    (lam := lam) (Lam := Lam) (BU := BU) (BV := BV)
    (Benergy :=
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        cubeAverage Q (coefficientEnergyDensity a v.grad))
    (BUtail := (5 * s⁻¹) * BU)
    (BVtail := (5 * s⁻¹) * BV)
    (Bforce :=
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
    hCmul_nonneg hs hs_le hweak hEll_desc hu_mem_desc hg_mem_desc
    hC_desc hData_desc hsum_desc hchildBdd huBdd_desc hgBdd_centered_desc
    hBdd hEll_open hData hsum_half havg_parent_nonneg havg_nonneg hint
    hmem hGlobalBdd hLocalBdd hBU_nonneg hBV_nonneg hu_tail hvConstructed
    hfluxV_bdd (by rfl) (by rfl) (by rfl) (by rfl) hbudget

/--
Exact-budget weak-flux correction with coefficient-energy average
nonnegativity derived from descendant ellipticity.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_exact_budget_of_descendant_isEllipticFieldOn
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    (C : ℝ) {lam Lam : ℝ}
    (hCmul_nonneg : 0 ≤ C)
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
    (hbudget :
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a v.grad) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (v.grad x)) ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  have havg_parent_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q a v.grad (hEll_desc Q ⟨0, by simp⟩)
  have havg_nonneg :
      ∀ n : ℕ, ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a v.grad) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_descendant_isEllipticFieldOn
      Q a v.grad hEll_desc
  exact
    cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_exact_budget
      Q a s g v C hCmul_nonneg hs hs_le hweak hEll_desc hu_mem_desc
      hg_mem_desc hC_desc hData_desc hsum_desc hchildBdd huBdd_desc
      hgBdd_centered_desc hBdd hEll_open hData hsum_half
      havg_parent_nonneg havg_nonneg hint hmem hGlobalBdd hLocalBdd
      hBU_nonneg hBV_nonneg hu_tail hvConstructed hfluxV_bdd hbudget

/-- Poincare radicand budgets closing into `C * correctionBound`. -/
theorem matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_const_mul_correctionBound_sq_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) (C s : ℝ)
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
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    (matNorm a0) ^ 2 *
        coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV ≤
      (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2 := by
  unfold coarseFluxResponseRHSPoincareExpandedRadicand
  nlinarith [henergy, hforce, hsum]

/-- Poincare square-root absorption into `C * correctionBound`. -/
theorem matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_radicand_le_sq
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {C s : ℝ}
    (g gradV : Vec d → Vec d)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hrad :
      (matNorm a0) ^ 2 *
          coarseFluxResponseRHSPoincareExpandedRadicand Q a s g gradV ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV ≤
      C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
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
    (mul_nonneg hC_nonneg
      (coarseFluxResponseRHSPoincareCorrectionBound_nonneg_of_bddAbove
        Q a a0 g hs hgBdd))
  simpa [hleft_sq] using hrad

/-- Poincare square-root absorption into `C * correctionBound` from budgets. -/
theorem matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_component_bounds
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {C s : ℝ}
    (g gradV : Vec d → Vec d)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
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
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV ≤
      C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g :=
  matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_radicand_le_sq
    Q a a0 g gradV hC_nonneg hs havg_nonneg hgBdd
    (matNorm_sq_mul_coarseFluxResponseRHSPoincareExpandedRadicand_le_const_mul_correctionBound_sq_of_component_bounds
      Q a a0 C s g gradV henergy hforce hsum)

/--
Poincare square-root absorption with the scalar side stated as the exact
matrix-weighted expanded budget.
-/
theorem matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_exact_budget
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {C s : ℝ}
    (g gradV : Vec d → Vec d)
    (hC_nonneg : 0 ≤ C) (hs : 0 < s)
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a gradV))
    (hgBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hbudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a gradV)) +
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g gradV ≤
      C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g :=
  matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_component_bounds
    (Q := Q) (a := a) (a0 := a0) (g := g) (gradV := gradV)
    (C := C) (s := s)
    (Benergy :=
      (matNorm a0) ^ 2 *
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a gradV)))
    (Bforce :=
      (matNorm a0) ^ 2 *
        (15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    hC_nonneg hs havg_nonneg hgBdd (by rfl) (by rfl) hbudget

/-- Constant-matrix gradient handoff to an arbitrary scalar envelope. -/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_le_of_grad_bound
    {d : ℕ} (Q : TriadicCube d) (a0 : Mat d)
    (s : ℝ) (gradV : Vec d → Vec d) {Bgrad B : ℝ}
    (hmat :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (gradV x)) ≤
        matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s gradV)
    (hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s gradV ≤ Bgrad)
    (hscalar : matNorm a0 * Bgrad ≤ B) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤ B := by
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x))
        ≤ matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s gradV := hmat
    _ ≤ matNorm a0 * Bgrad := by
          exact mul_le_mul_of_nonneg_left hgrad (matNorm_nonneg a0)
    _ ≤ B := hscalar

/--
H¹ weak-solution Poincare correction with the scalar side supplied as
matrix-weighted budgets closing into a caller-supplied multiple.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_const_mul_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    (C : ℝ) {lam Lam : ℝ}
    (hCmul_nonneg : 0 ≤ C)
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
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (v.grad x)) ≤
      C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  have havg_nonneg :
      0 ≤ cubeAverage Q (coefficientEnergyDensity a v.grad) :=
    cubeAverage_nonneg_of_nonneg_on (Q := Q)
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll v.grad)
  have hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s v.grad ≤
        coarseFluxResponseRHSPoincareExpandedBound Q a s g v.grad := by
    simpa [coarseFluxResponseRHSPoincareExpandedBound] using
      cubeBesovNegativeVectorSeminormTwo_grad_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := v)
        (s := s) (lam := lam) (Lam := Lam)
        hs hs_le hEll hweak hg hGlobalBdd
  have hmat :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (v.grad x)) ≤
        matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s v.grad :=
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le
      Q s a0 v.grad hgrad_mem_desc hgrad_bdd
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le_of_grad_bound
      Q a0 s v.grad hmat hgrad
      (matNorm_mul_coarseFluxResponseRHSPoincareExpandedBound_le_const_mul_correctionBound_of_component_bounds
        Q a a0 g v.grad hCmul_nonneg hs havg_nonneg hGlobalBdd
        henergy hforce hbudget)

/--
H¹ weak-solution Poincare correction with the scalar side stated as the exact
matrix-weighted expanded budget.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_const_mul_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_exact_budget
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (g : Vec d → Vec d) (v : H1Function (cubeSet Q))
    (C : ℝ) {lam Lam : ℝ}
    (hCmul_nonneg : 0 ≤ C)
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
    (hbudget :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q (coefficientEnergyDensity a v.grad)) +
        (matNorm a0) ^ 2 *
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) ≤
        (C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (v.grad x)) ≤
      C * coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g :=
  cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_const_mul_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
    (Q := Q) (a := a) (a0 := a0) (s := s) (g := g) (v := v) (C := C)
    (lam := lam) (Lam := Lam)
    (Benergy :=
      (matNorm a0) ^ 2 *
        (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          cubeAverage Q (coefficientEnergyDensity a v.grad)))
    (Bforce :=
      (matNorm a0) ^ 2 *
        (15000 * (s⁻¹) ^ 4 *
          ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))
    hCmul_nonneg hs hs_le hEll hweak hg hGlobalBdd hgrad_mem_desc
    hgrad_bdd (by rfl) (by rfl) hbudget

end

end Homogenization
