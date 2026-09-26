/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletHomogeneous
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedGlobalIteration

/-! # RHSConstant Apex Zero Dirichlet Corrected Weak Flux -/

@[expose] public section
namespace Homogenization

noncomputable section

/-!
# Corrected zero-Dirichlet weak-flux component route

This leaf is the live bridge from the zero-Dirichlet apex to the corrected
`Lambda * lambda^{-1}` weak-flux scalar surface.  It uses the corrector-energy
recurrence directly, avoiding the older absorbed forcing route whose displayed
force term has `Lambda^2` units.
-/

open scoped BigOperators ENNReal
namespace ZeroTraceDirichletCorrectorData

private theorem coarsePoincareRHSDepthWeight_nonneg (s : ℝ) (n : ℕ) :
    0 ≤ coarsePoincareRHSDepthWeight s n := by
  unfold coarsePoincareRHSDepthWeight
  exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _

theorem isEllipticFieldOn_descendant_cubeSet_of_parent
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hRdesc : ∃ n : ℕ, R ∈ descendantsAtDepth Q n) :
    IsEllipticFieldOn lam Lam (cubeSet R) a := by
  rcases hRdesc with ⟨n, hRn⟩
  exact IsEllipticFieldOn.mono hEll (measurableSet_cubeSet R)
    (cubeSet_subset_of_mem_descendantsAtDepth hRn)

private theorem weakFluxRHSLocalCorrectorEnergyErrorAverage_nonneg_of_descendant_ellipticity
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (z : TriadicCube d → Vec d → Vec d) {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (n : ℕ) :
    0 ≤ weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s n := by
  unfold weakFluxRHSLocalCorrectorEnergyErrorAverage
  exact descendantsAverage_nonneg Q n _ fun R hR => by
    unfold weakFluxRHSLocalCorrectorEnergyError
    exact mul_nonneg
      (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
        (weakFluxRHSLocalCoeff_nonneg R a hs))
      (cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        R a (z R)
          (isEllipticFieldOn_descendant_cubeSet_of_parent hEll ⟨n, hR⟩))

private theorem openCubeDescendantDeterministicCoarseData_of_descendant_depth
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDescendantDeterministicCoarseData Q a)
    (hRdesc : ∃ n : ℕ, R ∈ descendantsAtDepth Q n) :
    OpenCubeDescendantDeterministicCoarseData R a := by
  rcases hRdesc with ⟨n, hRn⟩
  have hRn_scale : R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) :=
    mem_descendantsAtScale_of_mem_descendantsAtDepth hRn
  have hn_scale : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  exact OpenCubeDescendantDeterministicCoarseData.of_mem_descendantsAtScale
    hData hn_scale hRn_scale

private theorem summable_qtwo_maxDescendantBBlockNormAtScale_of_descendant_depth
    {d : ℕ} {Q R : TriadicCube d} {a : CoeffField d} {s : ℝ}
    (hs : 0 < s)
    (hRdesc : ∃ n : ℕ, R ∈ descendantsAtDepth Q n)
    (hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a)) :
    Summable (fun m : ℕ =>
      geometricWeight s 2 m *
        maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a) := by
  rcases hRdesc with ⟨n, hRn⟩
  have hsum' :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a)
            (2 / 2 : ℝ)) := by
    simpa using hsum
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) :=
    mem_descendantsAtScale_sub_nat_of_mem_descendantsAtDepth hRn
  have hdesc :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale R (R.scale - (m : ℤ)) a)
            (2 / 2 : ℝ)) :=
    summable_geometricWeight_maxDescendantBBlockNormAtScale_rpow_q_div_two_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := Q.scale - (n : ℤ)) a s 2 hs.le
      (by norm_num) hRscale hsum'
  simpa using hdesc

private theorem weakFluxRHSScaledAveragedSeminormSq_bddAbove_of_flux_memLp
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {s : ℝ}
    (u : Vec d → Vec d) (hs : 0 < s)
    (hflux :
      MeasureTheory.MemLp (fun x => matVecMul (a x) (u x))
        (2 : ENNReal) (normalizedCubeMeasure Q)) :
    BddAbove (Set.range fun n : ℕ =>
      weakFluxRHSScaledAveragedSeminormSq Q a s u n) := by
  simpa [weakFluxRHSScaledAveragedSeminormSq, weakFluxRHSAveragedSeminormSq,
    coarsePoincareRHSSn, coarsePoincareRHSRn] using
      coarsePoincareRHSSn_bddAbove_of_memLp Q hs
        (fun x => matVecMul (a x) (u x)) hflux

private theorem zeroTraceDirichletWeakFluxCoefficientComponent_bound
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    ∀ k : ℕ,
      coarsePoincareRHSDepthWeight s k *
        weakFluxRHSLocalCoefficientEnergyErrorAverage Q a
          (fun x => ρ.toH10.toH1Function.grad x) s k ≤
        weakFluxRHSWeightedCoefficientEnergyBase Q a
          (fun x => ρ.toH10.toH1Function.grad x) s := by
  intro k
  have hs_half : 0 < s / 2 := by nlinarith
  have hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) 1) := by
    have hsum :
        Summable (fun m : ℕ =>
          geometricWeight (s / 2) 2 m *
            maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) :=
      summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
        (Q := Q) (a := a) (s := s / 2) hs_half hEll hData
    simpa [Real.rpow_one] using hsum
  have hEllOpen : IsEllipticFieldOn lam Lam (openCubeSet Q) a :=
    hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q k,
        0 ≤ cubeAverage R
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) := by
    intro R hR
    exact
      cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        R a (fun x => ρ.toH10.toH1Function.grad x)
        (isEllipticFieldOn_descendant_cubeSet_of_parent hEll ⟨k, hR⟩)
  have hint :
      MeasureTheory.IntegrableOn
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x))
        (cubeSet Q) MeasureTheory.volume :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  exact
    weakFluxRHSDepthWeight_mul_coefficientEnergyErrorAverage_le_weightedCoefficientEnergyBase
      Q a (fun x => ρ.toH10.toH1Function.grad x) k hs hEllOpen hData
      hsum_half havg_nonneg hint

/-- Displayed dimensional scale in the corrected zero-Dirichlet scalar budgets. -/
noncomputable def zeroTraceDirichletCorrectedWeakFluxApexDisplayScale
    (d : ℕ) (s : ℝ) : ℝ :=
  (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)

/-- Fixed internal scalar constant for the corrected zero-Dirichlet apex route. -/
noncomputable def zeroTraceDirichletCorrectedWeakFluxApexConstant
    (d : ℕ) (s : ℝ) : ℝ :=
  2000 * zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s

theorem zeroTraceDirichletCorrectedWeakFluxApexDisplayScale_nonneg
    (d : ℕ) (s : ℝ) :
    0 ≤ zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s := by
  unfold zeroTraceDirichletCorrectedWeakFluxApexDisplayScale
  exact mul_nonneg
    (by exact_mod_cast Nat.zero_le d)
    (mul_nonneg
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
      (Real.sqrt_nonneg 2))

theorem zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg
    (d : ℕ) (s : ℝ) :
    0 ≤ zeroTraceDirichletCorrectedWeakFluxApexConstant d s := by
  unfold zeroTraceDirichletCorrectedWeakFluxApexConstant
  exact mul_nonneg (by norm_num : 0 ≤ (2000 : ℝ))
    (zeroTraceDirichletCorrectedWeakFluxApexDisplayScale_nonneg d s)

theorem zeroTraceDirichletCorrectedWeakFluxApexPoincareConstant_sq
    (d : ℕ) (s : ℝ) :
    177500 *
        (zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s) ^ 2 ≤
      (zeroTraceDirichletCorrectedWeakFluxApexConstant d s) ^ 2 := by
  unfold zeroTraceDirichletCorrectedWeakFluxApexConstant
  nlinarith [sq_nonneg
    (zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s)]

/--
Localized zero-Dirichlet weak-flux estimate through the corrector-energy
component iteration.

The `u` coefficient-energy component is discharged internally from the
coefficient-localization bound; `hcorr` is the remaining Neumann-corrector
component input.  No `Lambda^2` absorbed-force estimate is used here.
-/
theorem localizedFluxDefectNegativeBesovAverageTwo_matVecMul_grad_le_sqrt_correctorEnergyComponents_of_selectors
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (s : ℝ) {Bcorr lam Lam : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (m : ℕ)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (z : TriadicCube d → Vec d → Vec d)
    (hzdecomp :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∃ w0 : AHarmonicFunction a (cubeSet R),
            z R = (fun x => ω.toH1MeanZero.toH1Function.grad x) ∧
            ∀ x ∈ cubeSet R,
              ρ.toH10.toH1Function.grad x =
                w0.toH1.grad x + z R x)
    (hcorr :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q a
            z s (m + k) ≤
          Bcorr) :
    localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) m ≤
      Real.sqrt
        ((coarsePoincareRHSDepthWeight s m)⁻¹ *
          ((weakFluxRHSWeightedCoefficientEnergyBase Q a
              (fun x => ρ.toH10.toH1Function.grad x) s + Bcorr) *
            (1 - Real.rpow (3 : ℝ) (-s))⁻¹)) := by
  have hBcoeff_nonneg :
      0 ≤ weakFluxRHSWeightedCoefficientEnergyBase Q a
        (fun x => ρ.toH10.toH1Function.grad x) s := by
    have havg_nonneg :
        0 ≤ cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) :=
      cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        Q a (fun x => ρ.toH10.toH1Function.grad x) hEll
    exact
      weakFluxRHSWeightedCoefficientEnergyBase_nonneg Q a
        (fun x => ρ.toH10.toH1Function.grad x) hs havg_nonneg
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam)
  have hData : OpenCubeDescendantDeterministicCoarseData Q a :=
    openCubeDescendantDeterministicCoarseData_of_recoveryFamily
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)
  have hsum :
      Summable (fun m : ℕ =>
        geometricWeight s 2 m *
          maxDescendantBBlockNormAtScale Q (Q.scale - (m : ℤ)) a) :=
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeDescendantDeterministicCoarseData
      (Q := Q) (a := a) s hs hEll hData
  have hcoeff :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s (m + k) *
          weakFluxRHSLocalCoefficientEnergyErrorAverage Q a
            (fun x => ρ.toH10.toH1Function.grad x) s (m + k) ≤
          weakFluxRHSWeightedCoefficientEnergyBase Q a
            (fun x => ρ.toH10.toH1Function.grad x) s := by
    intro k
    exact
      zeroTraceDirichletWeakFluxCoefficientComponent_bound
        (Q := Q) (a := a) (g := g) ρ hs hEll hData (m + k)
  have hBcorr_nonneg : 0 ≤ Bcorr := by
    have havg_nonneg :
        0 ≤ weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s m :=
      weakFluxRHSLocalCorrectorEnergyErrorAverage_nonneg_of_descendant_ellipticity
        (Q := Q) (a := a)
        (z := z)
        (s := s) (lam := lam) (Lam := Lam) hs hEll m
    have hleft_nonneg :
        0 ≤ coarsePoincareRHSDepthWeight s (m + 0) *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s (m + 0) := by
      simpa using
        mul_nonneg (coarsePoincareRHSDepthWeight_nonneg s m) havg_nonneg
    exact hleft_nonneg.trans (hcorr 0)
  have hρMemQ :
      MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ρ.toH10.toH1Function.grad_memVectorL2
  have hfluxMemQ :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hweakBdd :
      BddAbove (Set.range fun n : ℕ =>
        weakFluxRHSScaledAveragedSeminormSq Q a s
          (fun x => ρ.toH10.toH1Function.grad x) n) :=
    weakFluxRHSScaledAveragedSeminormSq_bddAbove_of_flux_memLp Q a
      (fun x => ρ.toH10.toH1Function.grad x) hs
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hfluxMemQ)
  have hchildBdd :
      ∀ R : TriadicCube d, (∃ n : ℕ, R ∈ descendantsAtDepth Q n) →
        ∀ S ∈ descendantsAtDepth R 1,
          BddAbove (Set.range fun N : ℕ =>
            cubeBesovNegativeVectorPartialSeminormTwo S s N
              (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))) := by
    intro R hRdesc S hS
    rcases hRdesc with ⟨j, hR⟩
    have hSQ : S ∈ descendantsAtDepth Q (j + 1) :=
      mem_descendantsAtDepth_add hR hS
    have hρMemS :
        MemVectorL2 (cubeSet S)
          (fun x => ρ.toH10.toH1Function.grad x) :=
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure S
        (memLp_on_descendant_of_memLp_generic (E := Vec d) hSQ hρMemQ)
    have hfluxMemS :
        MemVectorL2 (cubeSet S)
          (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn
        (isEllipticFieldOn_descendant_cubeSet_of_parent hEll ⟨j + 1, hSQ⟩)
        hρMemS
    exact
      cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp S hs
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))
        (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet S hfluxMemS)
  have hlocal :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        (cubeBesovNegativeVectorSeminormTwo R s
          (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))) ^ 2 ≤
          Real.rpow (3 : ℝ) (-2 * s) *
            descendantsAverage R 1
              (fun S =>
                (cubeBesovNegativeVectorSeminormTwo S s
                  (fun x =>
                    matVecMul (a x) (ρ.toH10.toH1Function.grad x))) ^ 2) +
          weakFluxRHSCorrectorEnergyLocalError R a
            (fun x => ρ.toH10.toH1Function.grad x)
            (z R) s := by
    intro j R hR
    have hRdesc : ∃ n : ℕ, R ∈ descendantsAtDepth Q n := ⟨j, hR⟩
    have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
      isEllipticFieldOn_descendant_cubeSet_of_parent hEll hRdesc
    have hρMemR :
        MemVectorL2 (cubeSet R)
          (fun x => ρ.toH10.toH1Function.grad x) :=
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
        (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hρMemQ)
    have hgMemR : MemVectorL2 (cubeSet R) g :=
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
        (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg)
    rcases hzdecomp j R hR with ⟨ωR, wR, hzR, hdecompR⟩
    have hflux :
        CubeAverageFluxEnergyControl R a
          (fun x => matVecMul (a x) (wR.toH1.grad x))
          (coefficientEnergyDensity a (fun x => wR.toH1.grad x)) := by
      simpa [scalarVariationEnergyIntegrand, coefficientEnergyDensity] using!
        cubeAverageFluxEnergyControl_of_aHarmonicFunction
          (Q := R) (a := a) hEllR wR
          (openCubeDescendantDeterministicCoarseData_of_descendant_depth
            hData hRdesc)
    have hdecompω :
        ∀ x ∈ cubeSet R,
          ρ.toH10.toH1Function.grad x =
            wR.toH1.grad x + ωR.toH1MeanZero.toH1Function.grad x := by
      simpa [hzR] using hdecompR
    have hstep :=
      ωR.sq_cubeBesovNegativeVectorSeminormTwo_flux_le_descendantsAverage_add_correctorEnergyLocalError_of_childBddAbove
        (u := fun x => ρ.toH10.toH1Function.grad x) wR s hs
        hEllR hρMemR hgMemR hflux
        (summable_qtwo_maxDescendantBBlockNormAtScale_of_descendant_depth
          hs hRdesc hsum)
        hdecompω (hchildBdd R hRdesc)
    simpa [hzR] using hstep
  exact
    localizedFluxDefectNegativeBesovAverageTwo_matVecMul_le_sqrt_of_scaled_correctorEnergyComponents_bddAbove
      (Q := Q) (a := a) (s := s)
      (u := fun x => ρ.toH10.toH1Function.grad x)
      (z := z)
      hs hlocal m hweakBdd hBcoeff_nonneg hBcorr_nonneg hcoeff hcorr

end ZeroTraceDirichletCorrectorData

end

end Homogenization
