/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHS
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedNoteApex

/-! # RHSCorrections -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# RHS correction components for the coarse-flux response split

This file contains the first correction-component bridge in manuscript §3.2.4.
The core split algebra stays in `CoarseFluxResponse.RHS`; here we import the
heavier §3.2.3 weak-flux RHS apex only where it is actually used.
-/

open scoped BigOperators ENNReal

/--
The expanded note-facing §3.2.3 weak-flux RHS used before it is absorbed into
the compact §3.2.4 weak-flux correction component.
-/
noncomputable def coarseFluxResponseRHSWeakFluxExpandedBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) (m : ℕ) (BU BV : ℝ) : ℝ :=
  Real.sqrt
    ((coarsePoincareRHSDepthWeight s m)⁻¹ *
      (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a gradV) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2))

/--
Depth-zero bridge from the localized §3.2.3 weak-flux output to the one-cube
`q = 2` component estimate used in the §3.2.4 split.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_localized_depth_zero
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d)
    (s : ℝ) (gradV g : Vec d → Vec d) {BU BV : ℝ}
    (hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (gradV x))))
    (hlocalized :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (gradV x)) 0 ≤
        coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV)
    (hscalar :
      coarseFluxResponseRHSWeakFluxExpandedBound Q a s g gradV 0 BU BV ≤
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (gradV x)) ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
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
    _ ≤ coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := hscalar

/--
The `a∇v` correction component in the §3.2.4 split, discharged from the
note-facing H¹ §3.2.3 weak-flux RHS apex.  The remaining scalar hypothesis is
the manuscript constant-absorption step comparing the expanded weak-flux RHS
with the compact §3.2.4 component.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_h1DirichletRhsWeakSolutionOn
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
    (hscalar :
      coarseFluxResponseRHSWeakFluxExpandedBound Q a s g v.grad 0 BU BV ≤
        coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (v.grad x)) ≤
      coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
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
    cubeBesovNegativeVectorSeminormTwo_matVecMul_le_coarseFluxResponseRHSWeakFluxCorrectionBound_of_localized_depth_zero
      Q a s v.grad g hfluxV_bdd hlocalized hscalar

/--
Frobenius control of a constant matrix acting on a vector.  This is the
pointwise algebraic core used to move a constant coarse matrix through the
note-normalized negative seminorm.
-/
theorem vecNormSq_matVecMul_le_matNormSq_mul_vecNormSq
    {d : ℕ} (A : Mat d) (ξ : Vec d) :
    vecNormSq (matVecMul A ξ) ≤ matNormSq A * vecNormSq ξ := by
  have hcalc :
      ∑ i, (∑ j, A i j * ξ j) ^ 2 ≤
        (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, (ξ j) ^ 2 := by
    calc
      ∑ i, (∑ j, A i j * ξ j) ^ 2
          ≤ ∑ i, (∑ j, (A i j) ^ 2) * ∑ j, (ξ j) ^ 2 := by
              refine Finset.sum_le_sum ?_
              intro i hi
              simpa [pow_two] using
                (Finset.sum_mul_sq_le_sq_mul_sq
                  (s := Finset.univ) (f := fun j => A i j) (g := ξ))
      _ = (∑ i, ∑ j, (A i j) ^ 2) * ∑ j, (ξ j) ^ 2 := by
            rw [Finset.sum_mul]
  simpa [vecNormSq, vecDot, matNormSq, matVecMul, pow_two] using hcalc

/--
The cube average commutes with applying a constant matrix to a vector field.
-/
theorem cubeAverageVec_matVecMul_const
    {d : ℕ} (Q : TriadicCube d) (A : Mat d) (u : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) :
    cubeAverageVec Q (fun x => matVecMul A (u x)) =
      matVecMul A (cubeAverageVec Q u) := by
  funext i
  have hui_int :
      ∀ j : Fin d,
        MeasureTheory.Integrable (fun x => u x j)
          (volumeMeasureOn (cubeSet Q)) := by
    intro j
    have huj :
        MeasureTheory.MemLp (fun x => u x j) (2 : ENNReal)
          (volumeMeasureOn (cubeSet Q)) := by
      simpa using! (ContinuousLinearMap.proj (R := ℝ) j).comp_memLp' hu
    exact huj.integrable (by norm_num : (1 : ENNReal) ≤ (2 : ENNReal))
  have hAui_int :
      ∀ j : Fin d,
        MeasureTheory.Integrable (fun x => A i j * u x j)
          (volumeMeasureOn (cubeSet Q)) := by
    intro j
    exact (hui_int j).const_mul (A i j)
  calc
    cubeAverageVec Q (fun x => matVecMul A (u x)) i
        = (cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, ∑ j, A i j * u x j ∂MeasureTheory.volume := by
              rfl
    _ = (cubeVolume Q)⁻¹ *
          ∑ j, ∫ x in cubeSet Q, A i j * u x j ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_finsetSum]
            intro j hj
            exact hAui_int j
    _ = (cubeVolume Q)⁻¹ *
          ∑ j, A i j * ∫ x in cubeSet Q, u x j ∂MeasureTheory.volume := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [MeasureTheory.integral_const_mul]
    _ = ∑ j, A i j *
          ((cubeVolume Q)⁻¹ *
            ∫ x in cubeSet Q, u x j ∂MeasureTheory.volume) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
    _ = matVecMul A (cubeAverageVec Q u) i := by
            simp [matVecMul, cubeAverageVec, cubeAverage]

/--
Depthwise action of a constant matrix on the `q = 2` negative Besov
descendant-average quantity.
-/
theorem cubeBesovNegativeVectorDepthAverage_constMatMul_le
    {d : ℕ} (Q : TriadicCube d) (A : Mat d) (u : Vec d → Vec d) (j : ℕ)
    (hu_desc :
      ∀ R ∈ descendantsAtDepth Q j, MemVectorL2 (cubeSet R) u) :
    cubeBesovNegativeVectorDepthAverage Q (fun x => matVecMul A (u x)) j ≤
      matNormSq A * cubeBesovNegativeVectorDepthAverage Q u j := by
  unfold cubeBesovNegativeVectorDepthAverage
  calc
    descendantsAverage Q j
        (fun R => vecNormSq (cubeAverageVec R (fun x => matVecMul A (u x))))
        ≤
      descendantsAverage Q j
        (fun R => matNormSq A * vecNormSq (cubeAverageVec R u)) := by
          refine descendantsAverage_le_descendantsAverage Q j ?_
          intro R hR
          calc
            vecNormSq (cubeAverageVec R (fun x => matVecMul A (u x)))
                = vecNormSq (matVecMul A (cubeAverageVec R u)) := by
                    rw [cubeAverageVec_matVecMul_const R A u (hu_desc R hR)]
            _ ≤ matNormSq A * vecNormSq (cubeAverageVec R u) :=
                  vecNormSq_matVecMul_le_matNormSq_mul_vecNormSq A (cubeAverageVec R u)
    _ =
      matNormSq A *
        descendantsAverage Q j (fun R => vecNormSq (cubeAverageVec R u)) := by
          rw [descendantsAverage_mul_left]

/--
Finite `q = 2` negative seminorm control under a constant matrix action.
-/
theorem cubeBesovNegativeVectorPartialSeminormTwo_constMatMul_le
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (A : Mat d)
    (u : Vec d → Vec d) (N : ℕ)
    (hu_desc :
      ∀ j ∈ Finset.range (N + 1), ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) u) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => matVecMul A (u x)) ≤
      matNorm A * cubeBesovNegativeVectorPartialSeminormTwo Q s N u := by
  have hsq :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul A (u x))) ^ 2 ≤
        matNormSq A *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 := by
    calc
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul A (u x))) ^ 2
          ≤
        ∑ j ∈ Finset.range (N + 1),
          (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
            (matNormSq A * cubeBesovNegativeVectorDepthAverage Q u j) := by
              refine
                sq_cubeBesovNegativeVectorPartialSeminormTwo_le_of_depthAverage_le
                  Q s N (fun x => matVecMul A (u x)) ?_
              intro j hj
              exact cubeBesovNegativeVectorDepthAverage_constMatMul_le
                Q A u j (fun R hR => hu_desc j hj R hR)
      _ =
        matNormSq A *
          ∑ j ∈ Finset.range (N + 1),
            (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
              cubeBesovNegativeVectorDepthAverage Q u j := by
            calc
              ∑ j ∈ Finset.range (N + 1),
                  (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                    (matNormSq A * cubeBesovNegativeVectorDepthAverage Q u j)
                  =
                ∑ j ∈ Finset.range (N + 1),
                  matNormSq A *
                    ((Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                      cubeBesovNegativeVectorDepthAverage Q u j) := by
                    refine Finset.sum_congr rfl ?_
                    intro j hj
                    ring
              _ =
                matNormSq A *
                  ∑ j ∈ Finset.range (N + 1),
                    (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 *
                      cubeBesovNegativeVectorDepthAverage Q u j := by
                    rw [Finset.mul_sum]
      _ =
        matNormSq A *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 := by
            congr 1
            rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact (sq_cubeBesovNegativeVectorDepthSeminorm Q s u j).symm
  have hright_sq :
      matNormSq A *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 =
        (matNorm A * cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 := by
    calc
      matNormSq A *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2
          =
        (Real.sqrt (matNormSq A)) ^ 2 *
          (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 := by
            rw [Real.sq_sqrt (matNormSq_nonneg A)]
      _ =
        (matNorm A * cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 := by
            rw [matNorm]
            ring
  have hleft_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => matVecMul A (u x)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N
      (fun x => matVecMul A (u x))
  have hright_nonneg :
      0 ≤ matNorm A * cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    mul_nonneg (matNorm_nonneg A)
      (cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u)
  nlinarith

/--
Full `q = 2` negative seminorm control under a constant matrix action.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_le
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (A : Mat d) (u : Vec d → Vec d)
    (hu_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j, MemVectorL2 (cubeSet R) u)
    (huBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N u)) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul A (u x)) ≤
      matNorm A * cubeBesovNegativeVectorSeminormTwo Q s u := by
  refine cubeBesovNegativeVectorSeminormTwo_le_of_partialBound Q s
    (fun x => matVecMul A (u x)) ?_
  intro N
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => matVecMul A (u x))
        ≤ matNorm A * cubeBesovNegativeVectorPartialSeminormTwo Q s N u := by
          exact cubeBesovNegativeVectorPartialSeminormTwo_constMatMul_le
            Q s A u N (fun j hj R hR => hu_desc j R hR)
    _ ≤ matNorm A * cubeBesovNegativeVectorSeminormTwo Q s u := by
          refine mul_le_mul_of_nonneg_left ?_ (matNorm_nonneg A)
          unfold cubeBesovNegativeVectorSeminormTwo
          exact le_csSup huBdd ⟨N, rfl⟩

/--
The expanded note-facing RHS Poincare bound before the constant-coefficient
correction `a₀∇v` is absorbed into the compact §3.2.4 Poincare component.
-/
noncomputable def coarseFluxResponseRHSPoincareExpandedBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g gradV : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        cubeAverage Q (coefficientEnergyDensity a gradV) +
      15000 * (s⁻¹) ^ 4 * ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

/--
Poincare-correction bridge from a gradient RHS Poincare bound plus a
constant-matrix action estimate to the `a₀∇v` component in the §3.2.4 split.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradV g : Vec d → Vec d) {Bgrad : ℝ}
    (hmat :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (gradV x)) ≤
        matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s gradV)
    (hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s gradV ≤ Bgrad)
    (hscalar :
      matNorm a0 * Bgrad ≤
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x))
        ≤ matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s gradV := hmat
    _ ≤ matNorm a0 * Bgrad := by
          exact mul_le_mul_of_nonneg_left hgrad (matNorm_nonneg a0)
    _ ≤ coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := hscalar

/--
Poincare-correction bridge where the constant-matrix action is discharged from
descendant-local `L²` data plus bounded finite negative seminorms.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound_and_descendant_mem
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (s : ℝ) (gradV g : Vec d → Vec d) {Bgrad : ℝ}
    (hgrad_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) gradV)
    (hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N gradV))
    (hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s gradV ≤ Bgrad)
    (hscalar :
      matNorm a0 * Bgrad ≤
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (gradV x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  have hmat :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (gradV x)) ≤
        matNorm a0 * cubeBesovNegativeVectorSeminormTwo Q s gradV :=
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le
      Q s a0 gradV hgrad_mem_desc hgrad_bdd
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound
      Q a a0 s gradV g hmat hgrad hscalar

/--
The `a₀∇v` correction component routed through the H¹ RHS Poincare theorem.
The constant-matrix action is discharged by the seminorm bridge above; the
remaining scalar hypothesis is the compact-manuscript absorption step.
-/
theorem cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn
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
    (hscalar :
      matNorm a0 * coarseFluxResponseRHSPoincareExpandedBound Q a s g v.grad ≤
        coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul a0 (v.grad x)) ≤
      coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g := by
  have hgrad :
      cubeBesovNegativeVectorSeminormTwo Q s v.grad ≤
        coarseFluxResponseRHSPoincareExpandedBound Q a s g v.grad := by
    simpa [coarseFluxResponseRHSPoincareExpandedBound] using
      cubeBesovNegativeVectorSeminormTwo_grad_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_h1DirichletRhsWeakSolutionOn
        (Q := Q) (a := a) (g := g) (u := v)
        (s := s) (lam := lam) (Lam := Lam)
        hs hs_le hEll hweak hg hGlobalBdd
  exact
    cubeBesovNegativeVectorSeminormTwo_constMatMul_le_coarseFluxResponseRHSPoincareCorrectionBound_of_grad_bound_and_descendant_mem
      Q a a0 s v.grad g hgrad_mem_desc hgrad_bdd hgrad hscalar

end

end Homogenization
