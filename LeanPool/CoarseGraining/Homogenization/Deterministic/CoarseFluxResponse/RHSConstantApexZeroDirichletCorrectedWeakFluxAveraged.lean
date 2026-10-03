/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.RHSConstantApexZeroDirichletCorrectedWeakFlux
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergyAveraged

/-! # RHSConstant Apex Zero Dirichlet Corrected Weak Flux Averaged -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Corrected zero-Dirichlet weak-flux apex with averaged corrector energy

This leaf consumes the proved averaged Neumann-corrector energy estimate in the
corrected zero-Dirichlet weak-flux route.  It removes the exposed
`hcorr`/`hcorrectorBudget` arguments from the previous component theorem and
constructs the descendant harmonic-remainder selector inside the apex.
-/

open scoped BigOperators ENNReal

namespace ZeroTraceDirichletCorrectorData

/--
The corrected weak-flux component with the averaged corrector-energy force
budget inserted directly.

This is the scalar repair that avoids the false comparison
`lambda^{-1} <= Lambda`: the coefficient-energy component is bounded by the
proved weak-flux energy compact scale, and the corrector-energy component is
bounded by its own proved `Lambda * lambda^{-1}` force scale.
-/
theorem cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_averagedCorrectorEnergy
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (C s : ℝ) {Bcorr lam Lam : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
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
        coarsePoincareRHSDepthWeight s k *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s k ≤
          Bcorr)
    (hcorrectorForceBudget :
      Bcorr * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        2500 * (s⁻¹) ^ 4 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)
    (hC_sq :
      32500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 +
        2500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        C ^ 2) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) ≤
      C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := by
  let Bcoeff : ℝ :=
    weakFluxRHSWeightedCoefficientEnergyBase Q a
      (fun x => ρ.toH10.toH1Function.grad x) s
  let H : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let LamQ : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let K : ℝ :=
    (Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * LamQ * L * G ^ 2
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have havg_nonneg :
      0 ≤ cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) :=
    cubeAverage_coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
      Q a (fun x => ρ.toH10.toH1Function.grad x) hEll
  have hBcoeff_nonneg : 0 ≤ Bcoeff := by
    dsimp [Bcoeff]
    exact
      weakFluxRHSWeightedCoefficientEnergyBase_nonneg Q a
        (fun x => ρ.toH10.toH1Function.grad x) hs havg_nonneg
  have hBcorr_nonneg : 0 ≤ Bcorr := by
    have havg_corr_nonneg :
        0 ≤ weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s 0 := by
      unfold weakFluxRHSLocalCorrectorEnergyErrorAverage
      exact descendantsAverage_nonneg Q 0 _ fun R hR => by
        unfold weakFluxRHSLocalCorrectorEnergyError
        have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
          hEll.mono (measurableSet_cubeSet R)
            (cubeSet_subset_of_mem_descendantsAtDepth hR)
        exact mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
            (weakFluxRHSLocalCoeff_nonneg R a hs))
          (cubeAverage_nonneg_of_nonneg_on
            (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEllR
              (z R)))
    have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s 0 := by
      unfold coarsePoincareRHSDepthWeight
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    exact (mul_nonneg hweight_nonneg havg_corr_nonneg).trans (hcorr 0)
  have hlocalized :
      localizedFluxDefectNegativeBesovAverageTwo Q s
          (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) 0 ≤
        Real.sqrt
          ((coarsePoincareRHSDepthWeight s 0)⁻¹ *
            ((Bcoeff + Bcorr) * H)) := by
    simpa [Bcoeff, H] using
      localizedFluxDefectNegativeBesovAverageTwo_matVecMul_grad_le_sqrt_correctorEnergyComponents_of_selectors
        (Q := Q) (a := a) (g := g) ρ (s := s)
        (Bcorr := Bcorr) (lam := lam) (Lam := Lam)
        hs hEll 0 hg z hzdecomp
        (by intro k; simpa using hcorr k)
  have hfluxV_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
      (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hfluxV_mem)
  have hseminorm_nonneg :
      0 ≤ cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
    cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s
      (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) hfluxV_bdd
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    have hr_lt_one : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  have hrad_nonneg : 0 ≤ (Bcoeff + Bcorr) * H :=
    mul_nonneg (add_nonneg hBcoeff_nonneg hBcorr_nonneg) hH_nonneg
  have htarget_nonneg :
      0 ≤ C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
    mul_nonneg hC_nonneg
      (coarseFluxResponseRHSWeakFluxCorrectionBound_nonneg_of_bddAbove
        Q a g hs hGlobalBdd)
  have henergyEnvelope :
      cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x)) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g :=
    ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd
  have hcoeffNote :
      Bcoeff * H ≤
        50 * (s⁻¹) ^ 2 * LamQ *
          cubeAverage Q
            (coefficientEnergyDensity a
              (fun x => ρ.toH10.toH1Function.grad x)) := by
    simpa [Bcoeff, H, LamQ] using
      weakFluxRHSWeightedCoefficientEnergyBase_mul_inv_one_sub_step_le_noteEnergySquare
        Q a (fun x => ρ.toH10.toH1Function.grad x) hs hs_le havg_nonneg
  have hcoeffMultiplier_nonneg :
      0 ≤ 50 * (s⁻¹) ^ 2 * LamQ := by
    dsimp [LamQ]
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (50 : ℝ)) (sq_nonneg (s⁻¹)))
        (multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
          (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ)))
  have hcoeffEnvelope :
      Bcoeff * H ≤
        50 * (s⁻¹) ^ 2 * LamQ *
          zeroTraceDirichletEnergyEnvelope Q a s g := by
    calc
      Bcoeff * H ≤
          50 * (s⁻¹) ^ 2 * LamQ *
            cubeAverage Q
              (coefficientEnergyDensity a
                (fun x => ρ.toH10.toH1Function.grad x)) := hcoeffNote
      _ ≤
          50 * (s⁻¹) ^ 2 * LamQ *
            zeroTraceDirichletEnergyEnvelope Q a s g := by
            exact mul_le_mul_of_nonneg_left henergyEnvelope hcoeffMultiplier_nonneg
  have henergyScale :
      50 * (s⁻¹) ^ 2 * LamQ *
          zeroTraceDirichletEnergyEnvelope Q a s g ≤
        (32500 * N ^ 2) * K := by
    simpa [LamQ, L, N, G, K, mul_assoc, mul_left_comm, mul_comm] using
      zeroTraceDirichletWeakFluxDisplayedEnergyScale_le_compact_sq
        Q a g hs hs_le hG_nonneg
  have hcorrectorScale :
      2500 * (s⁻¹) ^ 4 *
          LamQ * L * N ^ 2 * G ^ 2 ≤
        (2500 * N ^ 2) * K := by
    have hbase :
        2500 * (s⁻¹) ^ 4 * LamQ * L * N ^ 2 ≤
          (2500 * N ^ 2) *
            ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * LamQ * L) := by
      simpa [LamQ, L, N, mul_assoc, mul_left_comm, mul_comm] using
        zeroTraceDirichletWeakFluxDisplayedForceScale_le_compact_sq
          (Q := Q) (a := a) (s := s)
          (AweakForce := 2500 * N ^ 2) hs hs_le
          (by simp [N])
    have hscaled := mul_le_mul_of_nonneg_right hbase (sq_nonneg G)
    calc
      2500 * (s⁻¹) ^ 4 * LamQ * L * N ^ 2 * G ^ 2
          =
        (2500 * (s⁻¹) ^ 4 * LamQ * L * N ^ 2) * G ^ 2 := by ring
      _ ≤
        ((2500 * N ^ 2) *
            ((Real.rpow s (-(5 / 2 : ℝ))) ^ 2 * LamQ * L)) * G ^ 2 :=
          hscaled
      _ = (2500 * N ^ 2) * K := by
          dsimp [K]
          ring
  have hK_nonneg : 0 ≤ K := by
    have hLam_nonneg : 0 ≤ LamQ := by
      dsimp [LamQ]
      exact multiscale_ellipticity_LambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
    have hlambda_nonneg :
        0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
      multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
        (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
    dsimp [K, L]
    positivity
  have hcomponentBudget :
      (Bcoeff + Bcorr) * H ≤
        (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2 := by
    have hcoeffCompact : Bcoeff * H ≤ (32500 * N ^ 2) * K :=
      hcoeffEnvelope.trans henergyScale
    have hcorrCompact : Bcorr * H ≤ (2500 * N ^ 2) * K := by
      calc
        Bcorr * H ≤
            2500 * (s⁻¹) ^ 4 *
              LambdaSq Q (s / 2) (.finite 2) a *
              (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
              ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
              simpa [H] using hcorrectorForceBudget
        _ ≤ (2500 * N ^ 2) * K := by
              simpa [LamQ, L, N, G, mul_assoc, mul_left_comm, mul_comm] using
                hcorrectorScale
    have hsum :
        Bcoeff * H + Bcorr * H ≤
          (32500 * N ^ 2) * K + (2500 * N ^ 2) * K :=
      add_le_add hcoeffCompact hcorrCompact
    have halloc_scaled :
        (32500 * N ^ 2 + 2500 * N ^ 2) * K ≤ C ^ 2 * K :=
      mul_le_mul_of_nonneg_right hC_sq hK_nonneg
    calc
      (Bcoeff + Bcorr) * H = Bcoeff * H + Bcorr * H := by ring
      _ ≤ (32500 * N ^ 2) * K + (2500 * N ^ 2) * K := hsum
      _ = (32500 * N ^ 2 + 2500 * N ^ 2) * K := by ring
      _ ≤ C ^ 2 * K := halloc_scaled
      _ =
          (C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g) ^ 2 := by
          rw [const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_sq_eq
            Q a C g hs]
          dsimp [K, LamQ, L, G]
          ring
  have hsqrt :
      Real.sqrt ((Bcoeff + Bcorr) * H) ≤
        C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
    Real.sqrt_le_of_le_sq hrad_nonneg htarget_nonneg hcomponentBudget
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))
        =
      localizedFluxDefectNegativeBesovAverageTwo Q s
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) 0 := by
          exact
            (localizedFluxDefectNegativeBesovAverageTwo_depth_zero_of_nonneg
              Q s
              (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))
              hseminorm_nonneg).symm
    _ ≤ Real.sqrt
          ((coarsePoincareRHSDepthWeight s 0)⁻¹ *
            ((Bcoeff + Bcorr) * H)) := hlocalized
    _ = Real.sqrt ((Bcoeff + Bcorr) * H) := by
          simp [coarsePoincareRHSDepthWeight]
    _ ≤ C * coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g := hsqrt

/--
Zero-Dirichlet one-cube RHS apex with the weak-flux component routed directly
through the proved averaged corrector-energy budget.  The theorem no longer
exposes `Bcorr`, `hcorr`, `hcorrectorBudget`, or the invalid
`lambda^{-1} <= Lambda` comparison, and it constructs the descendant
`omega`/`w0` harmonic-remainder decomposition internally.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_correctedWeakFlux_averagedCorrectorEnergy
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    (a0 : Mat d) (s : ℝ) (gradU : Vec d → Vec d)
    (w : AHarmonicFunction a (cubeSet Q))
    {lam Lam lam0 Lam0 : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hgrad : ∀ x ∈ cubeSet Q,
      gradU x = w.toH1.grad x + ρ.toH10.toH1Function.grad x)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 gradU) ≤
      2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
        coarseFluxResponseRHSBound Q a a0 s gradU g := by
  classical
  let N : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let Bcorr : ℝ :=
    1000 * (geometricDiscount s 2)⁻¹ * (s⁻¹) ^ 2 *
      LambdaSq Q (s / 2) (.finite 2) a *
      (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
      N ^ 2 * G ^ 2
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  let IsDescendantOfQ : TriadicCube d → Prop :=
    fun R => ∃ n : ℕ, R ∈ descendantsAtDepth Q n
  have hρMemQ :
      MeasureTheory.MemLp (fun x => ρ.toH10.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ρ.toH10.toH1Function.grad_memVectorL2
  have hgMemQ : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg
  have hresidual :
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x) - g x) :=
    ρ.residualFlux_solenoidal hEll hgMemQ
  have hlocalSelector :
      ∀ R : TriadicCube d, IsDescendantOfQ R →
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∃ w0 : AHarmonicFunction a (cubeSet R),
            ∀ x ∈ cubeSet R,
              ρ.toH10.toH1Function.grad x =
                w0.toH1.grad x +
                  ω.toH1MeanZero.toH1Function.grad x := by
    intro R hRdesc
    rcases hRdesc with ⟨j, hR⟩
    have hEllR : IsEllipticFieldOn lam Lam (cubeSet R) a :=
      isEllipticFieldOn_descendant_cubeSet_of_parent hEll ⟨j, hR⟩
    have hρMemR :
        MemVectorL2 (cubeSet R)
          (fun x => ρ.toH10.toH1Function.grad x) :=
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
        (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hρMemQ)
    have hgMemR : MemVectorL2 (cubeSet R) g :=
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
        (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg)
    exact
      MeanZeroNeumannCorrectorData.exists_centeredCorrector_aHarmonicRemainder_of_parent_potential_solenoidal_h1CoerciveEstimate
        (P := Q) (R := R) (a := a) (g := g)
        (n := j) (lam := lam) (Lam := Lam)
        (u := fun x => ρ.toH10.toH1Function.grad x)
        ρ.toH10.toH1Function.isPotentialOn hresidual hR hEllR
        hρMemR hgMemR (h1CoerciveEstimate_cubeSet R)
  let z : TriadicCube d → Vec d → Vec d :=
    fun R =>
      if hR : IsDescendantOfQ R then
        fun x =>
          (Classical.choose (hlocalSelector R hR)).toH1MeanZero.toH1Function.grad x
      else
        0
  have hzdecomp :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        ∃ ω : MeanZeroNeumannCorrectorData R a
            (fun x => g x - cubeAverageVec R g),
          ∃ w0 : AHarmonicFunction a (cubeSet R),
            z R = (fun x => ω.toH1MeanZero.toH1Function.grad x) ∧
            ∀ x ∈ cubeSet R,
              ρ.toH10.toH1Function.grad x =
                w0.toH1.grad x + z R x := by
    intro j R hR
    have hRdesc : IsDescendantOfQ R := ⟨j, hR⟩
    let ωR : MeanZeroNeumannCorrectorData R a
        (fun x => g x - cubeAverageVec R g) :=
      Classical.choose (hlocalSelector R hRdesc)
    let wR : AHarmonicFunction a (cubeSet R) :=
      Classical.choose (Classical.choose_spec (hlocalSelector R hRdesc))
    have hzR :
        z R = fun x => ωR.toH1MeanZero.toH1Function.grad x := by
      simp [z, hRdesc, ωR]
    have hdecompR :
        ∀ x ∈ cubeSet R,
          ρ.toH10.toH1Function.grad x =
            wR.toH1.grad x + ωR.toH1MeanZero.toH1Function.grad x := by
      simpa [ωR, wR] using
        Classical.choose_spec
          (Classical.choose_spec (hlocalSelector R hRdesc))
    refine ⟨ωR, wR, hzR, ?_⟩
    intro x hx
    rw [hzR]
    exact hdecompR x hx
  have hcorr :
      ∀ k : ℕ,
        coarsePoincareRHSDepthWeight s k *
          weakFluxRHSLocalCorrectorEnergyErrorAverage Q a z s k ≤
          Bcorr := by
    intro k
    simpa [Bcorr, N, G] using
      weakFluxRHSDepthWeight_mul_correctorEnergyErrorAverage_le_forceScale
        (Q := Q) (a := a) (g := g) (s := s) (n := k)
        hs hs_le hEll hg hGlobalBdd
        z
        (by
          intro R hR
          rcases hzdecomp k R hR with ⟨ωR, _wR, hzR, _hdecompR⟩
          exact ⟨ωR, hzR⟩)
  have hcorrectorForceBudget :
      Bcorr * (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
        2500 * (s⁻¹) ^ 4 *
          LambdaSq Q (s / 2) (.finite 2) a *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          N ^ 2 * G ^ 2 := by
    simpa [Bcorr, N, G] using
      weakFluxRHSCorrectorEnergyForceScale_mul_inv_one_sub_step_le_noteForceScale
        (Q := Q) (a := a) (g := g) (s := s) hs hs_le
  have hC_nonneg :
      0 ≤ zeroTraceDirichletCorrectedWeakFluxApexConstant d s :=
    zeroTraceDirichletCorrectedWeakFluxApexConstant_nonneg d s
  have hweakFluxC_sq :
      32500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 +
        2500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        (zeroTraceDirichletCorrectedWeakFluxApexConstant d s) ^ 2 := by
    let Dscale : ℝ := zeroTraceDirichletCorrectedWeakFluxApexDisplayScale d s
    have hD_nonneg : 0 ≤ Dscale ^ 2 := sq_nonneg Dscale
    have hsmall :
        32500 * Dscale ^ 2 + 2500 * Dscale ^ 2 ≤ (2000 * Dscale) ^ 2 := by
      nlinarith [hD_nonneg]
    simpa [Dscale, zeroTraceDirichletCorrectedWeakFluxApexConstant,
      zeroTraceDirichletCorrectedWeakFluxApexDisplayScale,
      add_assoc, add_comm, add_left_comm] using hsmall
  have hweakρ :
      IsH1DirichletRhsWeakSolutionOn a (cubeSet Q)
        ρ.toH10.toH1Function g := by
    intro φ
    exact ρ.weakSolution φ
  have hgrad_mem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MemVectorL2 (cubeSet R) ρ.toH10.toH1Function.grad := by
    intro j R hR
    exact
      memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure R
        (memLp_on_descendant_of_memLp_generic (E := Vec d) hR hρMemQ)
  have hPoincareC_sq :
      177500 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 ≤
        (zeroTraceDirichletCorrectedWeakFluxApexConstant d s) ^ 2 := by
    simpa [zeroTraceDirichletCorrectedWeakFluxApexDisplayScale] using
      zeroTraceDirichletCorrectedWeakFluxApexPoincareConstant_sq d s
  rcases
      zeroTraceDirichletPoincareDisplayedComponentBoundsClose_of_const_ge
        (Q := Q) (a := a) (a0 := a0)
        (C := zeroTraceDirichletCorrectedWeakFluxApexConstant d s) (g := g)
        hs hs_le hG_nonneg hPoincareC_sq with
    ⟨BPoincareEnergy, BPoincareForce, hPoincareEnergyBudget,
      hPoincareForce, hPoincareBudget⟩
  have hgrad_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          ρ.toH10.toH1Function.grad) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
      ρ.toH10.toH1Function.grad hρMemQ
  have hfluxV_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll
      ρ.toH10.toH1Function.grad_memVectorL2
  have hfluxV_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
      (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x))
      (memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hfluxV_mem)
  have ha0Field :
      IsEllipticFieldOn lam0 Lam0 (cubeSet Q) (constantCoeffField a0) :=
    isEllipticFieldOn_constantCoeffField (measurableSet_cubeSet Q) ha0
  have hfluxW_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul (a x) (w.toH1.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
  have ha0W_mem :
      MemVectorL2 (cubeSet Q) (fun x => matVecMul a0 (w.toH1.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn ha0Field w.toH1.grad_memVectorL2
  have hdefectW_mem :
      MemVectorL2 (cubeSet Q) (fluxDefect a a0 w.toH1.grad) := by
    unfold fluxDefect
    exact hfluxW_mem.sub ha0W_mem
  have ha0V_mem :
      MemVectorL2 (cubeSet Q)
        (fun x => matVecMul a0 (ρ.toH10.toH1Function.grad x)) := by
    simpa [constantCoeffField] using
      memVectorL2_matVecMul_of_isEllipticFieldOn ha0Field
        ρ.toH10.toH1Function.grad_memVectorL2
  have hdefectW_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fluxDefect a a0 w.toH1.grad)) := by
    refine ⟨coarseFluxResponseQOneBound Q a a0 s w, ?_⟩
    rintro y ⟨N, rfl⟩
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_le_partialSeminorm
        Q s N (fluxDefect a a0 w.toH1.grad)).trans <| by
        simpa [fluxDefect, coarseFluxResponseQOneBound] using!
          coarseFluxResponse_qone_partialSeminorm_le_of_aHarmonicFunction
            (Q := Q) (a := a) (a0 := a0) (s := s)
            hs hEll ha0 ha0symm w hresponseSum N
  have ha0V_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul a0 (ρ.toH10.toH1Function.grad x))) := by
    rcases hgrad_bdd with ⟨M, hM⟩
    refine ⟨matNorm a0 * M, ?_⟩
    rintro y ⟨N0, rfl⟩
    calc
      cubeBesovNegativeVectorPartialSeminormTwo Q s N0
          (fun x => matVecMul a0 (ρ.toH10.toH1Function.grad x))
          ≤ matNorm a0 *
              cubeBesovNegativeVectorPartialSeminormTwo Q s N0
                ρ.toH10.toH1Function.grad := by
            exact cubeBesovNegativeVectorPartialSeminormTwo_constMatMul_le
              Q s a0 ρ.toH10.toH1Function.grad N0
              (fun j _ R hR => hgrad_mem_desc j R hR)
      _ ≤ matNorm a0 * M := by
            exact mul_le_mul_of_nonneg_left (hM ⟨N0, rfl⟩)
              (matNorm_nonneg a0)
  have henergyEnvelope :
      cubeAverage Q
          (coefficientEnergyDensity a ρ.toH10.toH1Function.grad) ≤
        zeroTraceDirichletEnergyEnvelope Q a s g :=
    ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd
  have hdisplay_ge_one :
      1 ≤
        (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2) :=
    one_le_zeroTraceDirichletDisplayScale_expr (d := d) (s := s) hs
  have hdisplay_nonneg :
      0 ≤ (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2) := by
    simpa [zeroTraceDirichletCorrectedWeakFluxApexDisplayScale] using
      zeroTraceDirichletCorrectedWeakFluxApexDisplayScale_nonneg d s
  have hhomogeneous :
      coarseFluxResponseQOneBound Q a a0 s w ≤
        zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g :=
    coarseFluxResponseQOneBound_le_const_mul_RHSHomogeneousSplitBound_of_zeroTraceDirichlet
      (Q := Q) (a := a) (g := g) ρ a0 s gradU w
      (lam := lam) (Lam := Lam)
      (C := zeroTraceDirichletCorrectedWeakFluxApexConstant d s)
      hs hs_le hEll hgrad hg hGlobalBdd
      (by
        unfold zeroTraceDirichletCorrectedWeakFluxApexConstant
          zeroTraceDirichletCorrectedWeakFluxApexDisplayScale
        nlinarith [hdisplay_ge_one])
      (by
        unfold zeroTraceDirichletCorrectedWeakFluxApexConstant
          zeroTraceDirichletCorrectedWeakFluxApexDisplayScale
        nlinarith [hdisplay_nonneg])
  have hfluxV :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (a x) (ρ.toH10.toH1Function.grad x)) ≤
        zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSWeakFluxCorrectionBound Q a s g :=
    cubeBesovNegativeVectorSeminormTwo_matVecMul_grad_le_const_mul_coarseFluxResponseRHSWeakFluxCorrectionBound_of_averagedCorrectorEnergy
      (Q := Q) (a := a) (g := g) ρ
      (C := zeroTraceDirichletCorrectedWeakFluxApexConstant d s) (s := s)
      (Bcorr := Bcorr) (lam := lam) (Lam := Lam) hC_nonneg
      hs hs_le hEll hg hGlobalBdd z hzdecomp hcorr
      (by simpa [N, G] using hcorrectorForceBudget)
      hweakFluxC_sq
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambdaInv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have hPoincareCoeff_nonneg :
      0 ≤ (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 *
            (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
    exact
      mul_nonneg (sq_nonneg (matNorm a0))
        (mul_nonneg
          (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
          hlambdaInv_nonneg)
  have hPoincareEnergy :
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q
              (coefficientEnergyDensity a ρ.toH10.toH1Function.grad)) ≤
        BPoincareEnergy := by
    calc
      (matNorm a0) ^ 2 *
          (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
            cubeAverage Q
              (coefficientEnergyDensity a ρ.toH10.toH1Function.grad))
          =
          ((matNorm a0) ^ 2 *
            (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            cubeAverage Q
              (coefficientEnergyDensity a ρ.toH10.toH1Function.grad) := by
            ring
      _ ≤
          ((matNorm a0) ^ 2 *
            (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹)) *
            zeroTraceDirichletEnergyEnvelope Q a s g := by
            exact mul_le_mul_of_nonneg_left henergyEnvelope hPoincareCoeff_nonneg
      _ =
          (matNorm a0) ^ 2 *
            (250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
              zeroTraceDirichletEnergyEnvelope Q a s g) := by
            ring
      _ ≤ BPoincareEnergy := hPoincareEnergyBudget
  have ha0V :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul a0 (ρ.toH10.toH1Function.grad x)) ≤
        zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSPoincareCorrectionBound Q a a0 s g :=
    cubeBesovNegativeVectorSeminormTwo_constMatMul_grad_le_const_mul_coarseFluxResponseRHSPoincareCorrectionBound_of_h1DirichletRhsWeakSolutionOn_of_component_bounds
      Q a a0 s g ρ.toH10.toH1Function
      (zeroTraceDirichletCorrectedWeakFluxApexConstant d s)
      hC_nonneg hs hs_le hEll
      hweakρ hg hGlobalBdd hgrad_mem_desc hgrad_bdd
      hPoincareEnergy hPoincareForce hPoincareBudget
  have hdefectW :
      cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 w.toH1.grad) ≤
        zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
          coarseFluxResponseRHSHomogeneousSplitBound Q a a0 s gradU g :=
    (cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_coarseFluxResponseQOneBound_of_aHarmonicFunction
      Q a a0 s hs hEll ha0 ha0symm w hresponseSum).trans
      hhomogeneous
  exact
    cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_const_mul_split_component_bounds
      Q a a0 gradU w.toH1.grad ρ.toH10.toH1Function.grad g
      hC_nonneg hs hGlobalBdd hgrad hdefectW_mem hfluxV_mem ha0V_mem
      hdefectW_bdd hfluxV_bdd ha0V_bdd hdefectW hfluxV ha0V

/--
PDE-facing corrected one-cube RHS apex with the zero-trace corrector and
harmonic split constructed internally from the weak solution.

This removes the non-proposition `ρ`, `w`, and decomposition arguments from
the corrected averaged route.
-/
private theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_h1DirichletRhsWeakSolutionOn_correctedWeakFlux_averagedCorrectorEnergy_of_memLp_of_bddAbove
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (a0 : Mat d) (s : ℝ) (g : Vec d → Vec d)
    (v : H1Function (cubeSet Q)) {lam Lam lam0 Lam0 : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 v.grad) ≤
      2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
        coarseFluxResponseRHSBound Q a a0 s v.grad g := by
  have hgMemQ : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg
  have hresidual :
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (a x) (v.grad x) - g x) :=
    hweak.residual_solenoidal hEll hgMemQ
  rcases
      ZeroTraceDirichletCorrectorData.exists_corrector_aHarmonicRemainder_of_parent_potential_solenoidal
        (Q := Q) (R := Q) (a := a) (g := g) (n := 0)
        (lam := lam) (Lam := Lam) (u := v.grad)
        v.isPotentialOn hresidual (by simp) hEll v.grad_memVectorL2 hgMemQ with
    ⟨ρ, w, hgrad⟩
  exact
    ρ.cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_correctedWeakFlux_averagedCorrectorEnergy
      (a0 := a0) (s := s) (gradU := v.grad) w
      hs hs_le hEll ha0 ha0symm hgrad hg hGlobalBdd hresponseSum

/--
PDE-facing corrected one-cube RHS apex with the zero-trace corrector and
harmonic split constructed internally, consuming the note-facing `H^s`
regularity package for the right-hand side.
-/
theorem cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_h1DirichletRhsWeakSolutionOn_correctedWeakFlux_averagedCorrectorEnergy
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    (a0 : Mat d) (s : ℝ) (g : Vec d → Vec d)
    (v : H1Function (cubeSet Q)) {lam Lam lam0 Lam0 : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0) (ha0symm : a0.IsSymm)
    (hweak : IsH1DirichletRhsWeakSolutionOn a (cubeSet Q) v g)
    (hg : CubeVectorBesovHRegularity Q s g)
    (hresponseSum :
      Summable (fun n : ℕ =>
        geometricWeight s 1 n *
          scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity a a0)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fluxDefect a a0 v.grad) ≤
      2 * zeroTraceDirichletCorrectedWeakFluxApexConstant d s *
        coarseFluxResponseRHSBound Q a a0 s v.grad g :=
  cubeBesovNegativeVectorSeminormTwo_fluxDefect_le_two_mul_const_mul_coarseFluxResponseRHSBound_of_h1DirichletRhsWeakSolutionOn_correctedWeakFlux_averagedCorrectorEnergy_of_memLp_of_bddAbove
    a0 s g v hs hs_le hEll ha0 ha0symm hweak hg.memLp
    hg.partialSeminorms_bddAbove hresponseSum

end ZeroTraceDirichletCorrectorData

end

end Homogenization
