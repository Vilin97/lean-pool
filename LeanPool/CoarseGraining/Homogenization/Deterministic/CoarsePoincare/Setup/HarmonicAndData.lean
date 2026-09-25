/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.EnergyControls
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Basic

/-! # Harmonic And Data -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped BigOperators

theorem cubeAverageFlux_le_coarseBBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet R) a (deterministicCoarseBlockMatrix (openCubeSet R) a))
    (hS : IsSigmaStarCoarse (openCubeSet R) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet R) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet R) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x))) ≤
      coarseBBlockNorm R a * cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  let : Fact (MeasureTheory.volume (cubeSet R) < ⊤) := by
    refine ⟨?_⟩
    simpa using volume_cubeSet_lt_top R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet R)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet R))
    infer_instance
  have hne : Set.Nonempty (cubeSet R) := by
    refine ⟨cubeCenter R, openCubeSet_subset_cubeSet R ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    simpa [Metric.mem_ball] using cubeRadius_pos R
  have hSCube : IsSigmaStarCoarse (cubeSet R) a sigmaStar :=
    (isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hS
  have hKCube : IsKappaCoarse (cubeSet R) a sigmaStar kappa :=
    (isKappaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hK
  have hSigmaCube : IsSigmaCoarse (cubeSet R) a sigma sigmaStar kappa :=
    (isSigmaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hSigma
  have hBCoarseEq :
      bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a) (kappaCoarse (cubeSet R) a) =
        bCoarse (sigmaCoarse (openCubeSet R) a) (sigmaStarCoarse (openCubeSet R) a)
          (kappaCoarse (openCubeSet R) a) := by
    exact
      bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
        (Q := R) hS hK hSigma hdet
  let hOpenR : IsOpenBoundedConvexDomain (openCubeSet R) :=
    isOpenBoundedConvexDomain_openCubeSet R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using hOpenR.isFiniteMeasure_restrict_volume
  have hEllOpen :
      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have hBdet :
      IsUnit
        (bCoarse (sigmaCoarse (openCubeSet R) a) (sigmaStarCoarse (openCubeSet R) a)
          (kappaCoarse (openCubeSet R) a)).det := by
    have hvolOpen : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
      rw [volume_openCubeSet_toReal]
      exact (cubeVolume_pos R).ne'
    exact
      isUnit_det_bCoarse_canonical_of_isEllipticFieldOn_of_isSobolevRegularDomain
        (U := openCubeSet R) (a := a) hOpenR.isSobolevRegularDomain hEllOpen hvolOpen
        hA hS hK hSigma hdet
  have hBdetCube :
      IsUnit
        (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
          (kappaCoarse (cubeSet R) a)).det := by
    simpa [hBCoarseEq] using hBdet
  have hv :
      Nonempty
        (ScalarCanonicalMaximizer (cubeSet R)
          (-matVecMul (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a))⁻¹
            (fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)))
          0 a) := by
    exact
      ScalarCanonicalMaximizer.nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
        (U := cubeSet R) (a := a) hne
        (hodgeConverseCriterion_cubeSet_triadicCube R) hEll _ _
  rcases hv with ⟨v⟩
  let B :=
    bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a) (kappaCoarse (cubeSet R) a)
  let avgFlux : Vec d :=
    fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)
  have havg_eq : cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x)) = avgFlux := by
    funext i
    simp [avgFlux, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
  have henergy :
      vecDot avgFlux (matVecMul B⁻¹ avgFlux) ≤
        volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
    have hraw :=
      ScalarCanonicalMaximizer.energyAverageFluxCanonicalOfIsSigmaCoarse
        (U := cubeSet R) (a := a) hEll hSCube hKCube hSigmaCube hdet
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w v
    simpa [avgFlux, B] using (show
      vecDot avgFlux (matVecMul B⁻¹ avgFlux) ≤
        volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) from by
          nlinarith [hraw])
  have hleftInv :
      ∀ ξ : Vec d, matVecMul B (matVecMul B⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hBdetCube]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hflux :
      vecNormSq avgFlux ≤ matNorm B * vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
    exact vecNormSq_le_matNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := B⁻¹) (B := B)
      (bCoarse_canonical_posSemidef_of_isSigmaCoarse (U := cubeSet R) (a := a) hSCube hKCube hSigmaCube hdet)
      hleftInv avgFlux
  have hB_eq_open :
      bCoarse (sigmaCoarse (openCubeSet R) a) (sigmaStarCoarse (openCubeSet R) a)
          (kappaCoarse (openCubeSet R) a) =
        bCoarse sigma sigmaStar kappa := by
    rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
      eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
      eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  have hnorm_eq : matNorm B = coarseBBlockNorm R a := by
    unfold coarseBBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a,
      coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix hA hS hK hSigma hdet]
    calc
      matNorm B =
          matNorm
            (bCoarse (sigmaCoarse (openCubeSet R) a) (sigmaStarCoarse (openCubeSet R) a)
              (kappaCoarse (openCubeSet R) a)) := by
            simpa [B] using congrArg matNorm hBCoarseEq
      _ = matNorm (bCoarse sigma sigmaStar kappa) := by rw [hB_eq_open]
  have henergy_eq :
      volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) =
        cubeAverage R (scalarVariationEnergyIntegrand a w) :=
    volumeAverage_cubeSet_eq_cubeAverage R (scalarVariationEnergyIntegrand a w)
  calc
    vecNormSq (cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x))) =
        vecNormSq avgFlux := by rw [havg_eq]
    _ ≤ matNorm B * vecDot avgFlux (matVecMul B⁻¹ avgFlux) := hflux
    _ ≤ matNorm B * volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
          exact mul_le_mul_of_nonneg_left henergy (matNorm_nonneg _)
    _ = coarseBBlockNorm R a * cubeAverage R (scalarVariationEnergyIntegrand a w) := by
          rw [hnorm_eq, henergy_eq]

theorem cubeAverageFlux_le_matrixNorm_bCoarse_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet R) a (deterministicCoarseBlockMatrix (openCubeSet R) a))
    (hS : IsSigmaStarCoarse (openCubeSet R) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet R) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet R) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det)
    (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x))) ≤
      Book.Ch02.matrixNorm
          (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a)) *
        cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  let : Fact (MeasureTheory.volume (cubeSet R) < ⊤) := by
    refine ⟨?_⟩
    simpa using volume_cubeSet_lt_top R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet R)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet R))
    infer_instance
  have hne : Set.Nonempty (cubeSet R) := by
    refine ⟨cubeCenter R, openCubeSet_subset_cubeSet R ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    simpa [Metric.mem_ball] using cubeRadius_pos R
  have hSCube : IsSigmaStarCoarse (cubeSet R) a sigmaStar :=
    (isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hS
  have hKCube : IsKappaCoarse (cubeSet R) a sigmaStar kappa :=
    (isKappaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hK
  have hSigmaCube : IsSigmaCoarse (cubeSet R) a sigma sigmaStar kappa :=
    (isSigmaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hSigma
  have hBCoarseEq :
      bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a) (kappaCoarse (cubeSet R) a) =
        bCoarse (sigmaCoarse (openCubeSet R) a) (sigmaStarCoarse (openCubeSet R) a)
          (kappaCoarse (openCubeSet R) a) := by
    exact
      bCoarse_sigmaCoarse_sigmaStarCoarse_kappaCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaCoarse
        (Q := R) hS hK hSigma hdet
  let hOpenR : IsOpenBoundedConvexDomain (openCubeSet R) :=
    isOpenBoundedConvexDomain_openCubeSet R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) := by
    simpa [volumeMeasureOn] using hOpenR.isFiniteMeasure_restrict_volume
  have hEllOpen :
      IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have hBdet :
      IsUnit
        (bCoarse (sigmaCoarse (openCubeSet R) a) (sigmaStarCoarse (openCubeSet R) a)
          (kappaCoarse (openCubeSet R) a)).det := by
    have hvolOpen : (MeasureTheory.volume (openCubeSet R)).toReal ≠ 0 := by
      rw [volume_openCubeSet_toReal]
      exact (cubeVolume_pos R).ne'
    exact
      isUnit_det_bCoarse_canonical_of_isEllipticFieldOn_of_isSobolevRegularDomain
        (U := openCubeSet R) (a := a) hOpenR.isSobolevRegularDomain hEllOpen hvolOpen
        hA hS hK hSigma hdet
  have hBdetCube :
      IsUnit
        (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
          (kappaCoarse (cubeSet R) a)).det := by
    simpa [hBCoarseEq] using hBdet
  have hv :
      Nonempty
        (ScalarCanonicalMaximizer (cubeSet R)
          (-matVecMul (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a))⁻¹
            (fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)))
          0 a) := by
    exact
      ScalarCanonicalMaximizer.nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
        (U := cubeSet R) (a := a) hne
        (hodgeConverseCriterion_cubeSet_triadicCube R) hEll _ _
  rcases hv with ⟨v⟩
  let B :=
    bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a) (kappaCoarse (cubeSet R) a)
  let avgFlux : Vec d :=
    fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)
  have havg_eq : cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x)) = avgFlux := by
    funext i
    simp [avgFlux, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
  have henergy :
      vecDot avgFlux (matVecMul B⁻¹ avgFlux) ≤
        volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
    have hraw :=
      ScalarCanonicalMaximizer.energyAverageFluxCanonicalOfIsSigmaCoarse
        (U := cubeSet R) (a := a) hEll hSCube hKCube hSigmaCube hdet
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w v
    simpa [avgFlux, B] using (show
      vecDot avgFlux (matVecMul B⁻¹ avgFlux) ≤
        volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) from by
          nlinarith [hraw])
  have hleftInv :
      ∀ ξ : Vec d, matVecMul B (matVecMul B⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hBdetCube]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hflux :
      vecNormSq avgFlux ≤
        Book.Ch02.matrixNorm B * vecDot avgFlux (matVecMul B⁻¹ avgFlux) := by
    exact Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := B⁻¹) (B := B)
      (bCoarse_canonical_posSemidef_of_isSigmaCoarse (U := cubeSet R) (a := a) hSCube hKCube hSigmaCube hdet)
      hleftInv avgFlux
  have henergy_eq :
      volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) =
        cubeAverage R (scalarVariationEnergyIntegrand a w) :=
    volumeAverage_cubeSet_eq_cubeAverage R (scalarVariationEnergyIntegrand a w)
  calc
    vecNormSq (cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x))) =
        vecNormSq avgFlux := by rw [havg_eq]
    _ ≤ Book.Ch02.matrixNorm B * vecDot avgFlux (matVecMul B⁻¹ avgFlux) := hflux
    _ ≤ Book.Ch02.matrixNorm B * volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
          exact mul_le_mul_of_nonneg_left henergy (Book.Ch02.matrixNorm_nonneg B)
    _ =
        Book.Ch02.matrixNorm
            (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
              (kappaCoarse (cubeSet R) a)) *
          cubeAverage R (scalarVariationEnergyIntegrand a w) := by
          rw [henergy_eq]

/--
Flux coarse-square estimate with the deterministic open-cube coarse witnesses
packaged as `OpenCubeDeterministicCoarseData`.
-/
theorem cubeAverageFlux_le_coarseBBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hData : OpenCubeDeterministicCoarseData R a)
    (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x))) ≤
      coarseBBlockNorm R a * cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    cubeAverageFlux_le_coarseBBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEll hA hS hK hSigma hdet w

theorem cubeAverageFlux_le_matrixNorm_bCoarse_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hData : OpenCubeDeterministicCoarseData R a)
    (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x))) ≤
      Book.Ch02.matrixNorm
          (bCoarse (sigmaCoarse (cubeSet R) a) (sigmaStarCoarse (cubeSet R) a)
            (kappaCoarse (cubeSet R) a)) *
        cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    cubeAverageFlux_le_matrixNorm_bCoarse_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEll hA hS hK hSigma hdet w

theorem cubeAverageGradient_le_coarseSigmaStarInvBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet R) a (deterministicCoarseBlockMatrix (openCubeSet R) a))
    (hS : IsSigmaStarCoarse (openCubeSet R) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet R) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet R) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => w.toH1.grad x)) ≤
      coarseSigmaStarInvBlockNorm R a * cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  let hInt : ResponseLinearIntegrabilityData (cubeSet R) a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hvol : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hSCube : IsSigmaStarCoarse (cubeSet R) a sigmaStar :=
    (isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hS
  have hKCube : IsKappaCoarse (cubeSet R) a sigmaStar kappa :=
    (isKappaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hK
  have hSigmaCube : IsSigmaCoarse (cubeSet R) a sigma sigmaStar kappa :=
    (isSigmaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hSigma
  let avgGrad : Vec d := fun i => volumeAverage (cubeSet R) (fun x => w.toH1.grad x i)
  let qbar : Vec d := matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad
  have havg_eq : cubeAverageVec R (fun x => w.toH1.grad x) = avgGrad := by
    funext i
    simp [avgGrad, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
  have hpairing :
      volumeAverage (cubeSet R) (fun x => vecDot qbar (w.toH1.grad x)) =
        vecDot qbar avgGrad := by
    have hpair :=
      basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
        (cubeSet R) a 0 qbar hInt w
    have hzero_left :
        volumeAverage (cubeSet R)
            (fun x => vecDot (0 : Vec d) (matVecMul (a x) (w.toH1.grad x))) = 0 := by
      rw [show (fun x => vecDot (0 : Vec d) (matVecMul (a x) (w.toH1.grad x))) = fun _ => (0 : ℝ) by
        funext x
        rw [vecDot]
        simp]
      exact volumeAverage_zero (cubeSet R)
    have hzero_right :
        vecDot (0 : Vec d)
            (fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)) = 0 := by
      rw [vecDot]
      simp
    nlinarith [hpair, hzero_left, hzero_right]
  have henergyInt :
      MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) (cubeSet R)
        MeasureTheory.volume :=
    ResponseLinearIntegrabilityData.energy hInt w
  have hgradInt :
      MeasureTheory.IntegrableOn (fun x => vecDot qbar (w.toH1.grad x)) (cubeSet R)
        MeasureTheory.volume :=
    hInt.grad qbar w
  have hresp_le :
      volumeAverage (cubeSet R) (scalarResponseIntegrand (cubeSet R) a 0 qbar w) ≤
        ResponseJ (cubeSet R) 0 qbar a := by
    exact
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEll hvol 0 qbar (responseJValueSet_mem (cubeSet R) 0 qbar a w)
  have hresp_lhs :
      volumeAverage (cubeSet R) (scalarResponseIntegrand (cubeSet R) a 0 qbar w) =
        (-(1 / 2 : ℝ)) * volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) +
          vecDot qbar avgGrad := by
    have hdecomp :
        scalarResponseIntegrand (cubeSet R) a 0 qbar w =
          (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a w) +
            fun x => vecDot qbar (w.toH1.grad x)) := by
      funext x
      unfold scalarResponseIntegrand scalarVariationEnergyIntegrand
      rw [show vecDot (0 : Vec d) (matVecMul (a x) (w.toH1.grad x)) = 0 by
        rw [vecDot]
        simp]
      simp [Pi.smul_apply]
    rw [hdecomp, volumeAverage_add]
    · rw [volumeAverage_smul, hpairing]
    · simpa [MeasureTheory.IntegrableOn] using
        (henergyInt.integrable.smul (-(1 / 2 : ℝ)))
    · exact hgradInt
  have hleftInv :
      ∀ ξ : Vec d,
        matVecMul (sigmaStarInvCoarse (cubeSet R) a)
          (matVecMul (sigmaStarCoarse (cubeSet R) a) ξ) = ξ := by
    intro ξ
    rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSCube,
      eq_sigmaStarCoarse_of_isSigmaStarCoarse hSCube hdet, matVecMul_mul,
      Matrix.nonsing_inv_mul sigmaStar hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hqbar :
      matVecMul (sigmaStarInvCoarse (cubeSet R) a) qbar = avgGrad := by
    simpa [qbar] using hleftInv avgGrad
  have hresp_rhs :
      ResponseJ (cubeSet R) 0 qbar a =
        (1 / 2 : ℝ) * vecDot avgGrad
          (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
    have hresp :=
      basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
        (cubeSet R) a hSCube hKCube hSigmaCube hdet 0 qbar
    calc
      ResponseJ (cubeSet R) 0 qbar a =
          (1 / 2 : ℝ) * vecDot qbar
            (matVecMul (sigmaStarInvCoarse (cubeSet R) a) qbar) := by
              simpa [qbar, vecDot, matVecMul]
                using hresp
      _ = (1 / 2 : ℝ) * vecDot qbar avgGrad := by rw [hqbar]
      _ = (1 / 2 : ℝ) * vecDot avgGrad
            (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
              simp [qbar, vecDot_comm]
  have henergy :
      vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) ≤
        volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
    rw [hresp_lhs, hresp_rhs] at hresp_le
    have hpairing' :
        vecDot qbar avgGrad =
          vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
      simp [qbar, vecDot_comm]
    rw [hpairing'] at hresp_le
    nlinarith
  have hgrad :
      vecNormSq avgGrad ≤
        matNorm (sigmaStarInvCoarse (cubeSet R) a) *
          vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
    exact vecNormSq_le_matNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := sigmaStarCoarse (cubeSet R) a) (B := sigmaStarInvCoarse (cubeSet R) a)
      (sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := cubeSet R) (a := a) hSCube)
      hleftInv avgGrad
  have hcanonRsig : sigmaStar⁻¹ = sigmaStarInvCoarse (cubeSet R) a := by
    calc
      sigmaStar⁻¹ = sigmaStarInvCoarse (openCubeSet R) a := by
        symm
        rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS]
      _ = sigmaStarInvCoarse (cubeSet R) a := by
        symm
        rw [sigmaStarInvCoarse_cubeSet_eq_openCubeSet_of_triadicCube_of_isSigmaStarCoarse
          (Q := R) (a := a) hS]
  have hnorm_eq :
      matNorm (sigmaStarInvCoarse (cubeSet R) a) = coarseSigmaStarInvBlockNorm R a := by
    unfold coarseSigmaStarInvBlockNorm
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a,
      coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix hA hS hK hSigma hdet,
      hcanonRsig]
  have henergy_eq :
      volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) =
        cubeAverage R (scalarVariationEnergyIntegrand a w) :=
    volumeAverage_cubeSet_eq_cubeAverage R (scalarVariationEnergyIntegrand a w)
  calc
    vecNormSq (cubeAverageVec R (fun x => w.toH1.grad x)) = vecNormSq avgGrad := by
      rw [havg_eq]
    _ ≤
        matNorm (sigmaStarInvCoarse (cubeSet R) a) *
          vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := hgrad
    _ ≤
        matNorm (sigmaStarInvCoarse (cubeSet R) a) *
          volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
            exact mul_le_mul_of_nonneg_left henergy (matNorm_nonneg _)
    _ = coarseSigmaStarInvBlockNorm R a * cubeAverage R (scalarVariationEnergyIntegrand a w) := by
      rw [hnorm_eq, henergy_eq]

theorem cubeAverageGradient_le_matrixNorm_sigmaStarInv_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    {sigma sigmaStar kappa : Mat d}
    (_hA : IsCoarseBlockMatrix (openCubeSet R) a (deterministicCoarseBlockMatrix (openCubeSet R) a))
    (hS : IsSigmaStarCoarse (openCubeSet R) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet R) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet R) a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => w.toH1.grad x)) ≤
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) a) *
        cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  let hInt : ResponseLinearIntegrabilityData (cubeSet R) a :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  have hvol : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hSCube : IsSigmaStarCoarse (cubeSet R) a sigmaStar :=
    (isSigmaStarCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hS
  have hKCube : IsKappaCoarse (cubeSet R) a sigmaStar kappa :=
    (isKappaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hK
  have hSigmaCube : IsSigmaCoarse (cubeSet R) a sigma sigmaStar kappa :=
    (isSigmaCoarse_cubeSet_iff_openCubeSet_of_triadicCube (Q := R)).2 hSigma
  let avgGrad : Vec d := fun i => volumeAverage (cubeSet R) (fun x => w.toH1.grad x i)
  let qbar : Vec d := matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad
  have havg_eq : cubeAverageVec R (fun x => w.toH1.grad x) = avgGrad := by
    funext i
    simp [avgGrad, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
  have hpairing :
      volumeAverage (cubeSet R) (fun x => vecDot qbar (w.toH1.grad x)) =
        vecDot qbar avgGrad := by
    have hpair :=
      basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
        (cubeSet R) a 0 qbar hInt w
    have hzero_left :
        volumeAverage (cubeSet R)
            (fun x => vecDot (0 : Vec d) (matVecMul (a x) (w.toH1.grad x))) = 0 := by
      rw [show (fun x => vecDot (0 : Vec d) (matVecMul (a x) (w.toH1.grad x))) = fun _ => (0 : ℝ) by
        funext x
        rw [vecDot]
        simp]
      exact volumeAverage_zero (cubeSet R)
    have hzero_right :
        vecDot (0 : Vec d)
            (fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)) = 0 := by
      rw [vecDot]
      simp
    nlinarith [hpair, hzero_left, hzero_right]
  have henergyInt :
      MeasureTheory.IntegrableOn (scalarVariationEnergyIntegrand a w) (cubeSet R)
        MeasureTheory.volume :=
    ResponseLinearIntegrabilityData.energy hInt w
  have hgradInt :
      MeasureTheory.IntegrableOn (fun x => vecDot qbar (w.toH1.grad x)) (cubeSet R)
        MeasureTheory.volume :=
    hInt.grad qbar w
  have hresp_le :
      volumeAverage (cubeSet R) (scalarResponseIntegrand (cubeSet R) a 0 qbar w) ≤
        ResponseJ (cubeSet R) 0 qbar a := by
    exact
      le_responseJ_of_mem_responseJValueSet_of_isEllipticFieldOn
        hEll hvol 0 qbar (responseJValueSet_mem (cubeSet R) 0 qbar a w)
  have hresp_lhs :
      volumeAverage (cubeSet R) (scalarResponseIntegrand (cubeSet R) a 0 qbar w) =
        (-(1 / 2 : ℝ)) * volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) +
          vecDot qbar avgGrad := by
    have hdecomp :
        scalarResponseIntegrand (cubeSet R) a 0 qbar w =
          (((-(1 / 2 : ℝ)) • scalarVariationEnergyIntegrand a w) +
            fun x => vecDot qbar (w.toH1.grad x)) := by
      funext x
      unfold scalarResponseIntegrand scalarVariationEnergyIntegrand
      rw [show vecDot (0 : Vec d) (matVecMul (a x) (w.toH1.grad x)) = 0 by
        rw [vecDot]
        simp]
      simp [Pi.smul_apply]
    rw [hdecomp, volumeAverage_add]
    · rw [volumeAverage_smul, hpairing]
    · simpa [MeasureTheory.IntegrableOn] using
        (henergyInt.integrable.smul (-(1 / 2 : ℝ)))
    · exact hgradInt
  have hleftInv :
      ∀ ξ : Vec d,
        matVecMul (sigmaStarInvCoarse (cubeSet R) a)
          (matVecMul (sigmaStarCoarse (cubeSet R) a) ξ) = ξ := by
    intro ξ
    rw [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hSCube,
      eq_sigmaStarCoarse_of_isSigmaStarCoarse hSCube hdet, matVecMul_mul,
      Matrix.nonsing_inv_mul sigmaStar hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hqbar :
      matVecMul (sigmaStarInvCoarse (cubeSet R) a) qbar = avgGrad := by
    simpa [qbar] using hleftInv avgGrad
  have hresp_rhs :
      ResponseJ (cubeSet R) 0 qbar a =
        (1 / 2 : ℝ) * vecDot avgGrad
          (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
    have hresp :=
      basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
        (cubeSet R) a hSCube hKCube hSigmaCube hdet 0 qbar
    calc
      ResponseJ (cubeSet R) 0 qbar a =
          (1 / 2 : ℝ) * vecDot qbar
            (matVecMul (sigmaStarInvCoarse (cubeSet R) a) qbar) := by
              simpa [qbar, vecDot, matVecMul]
                using hresp
      _ = (1 / 2 : ℝ) * vecDot qbar avgGrad := by rw [hqbar]
      _ = (1 / 2 : ℝ) * vecDot avgGrad
            (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
              simp [qbar, vecDot_comm]
  have henergy :
      vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) ≤
        volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
    rw [hresp_lhs, hresp_rhs] at hresp_le
    have hpairing' :
        vecDot qbar avgGrad =
          vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
      simp [qbar, vecDot_comm]
    rw [hpairing'] at hresp_le
    nlinarith
  have hgrad :
      vecNormSq avgGrad ≤
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) a) *
          vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := by
    exact Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      (A := sigmaStarCoarse (cubeSet R) a) (B := sigmaStarInvCoarse (cubeSet R) a)
      (sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := cubeSet R) (a := a) hSCube)
      hleftInv avgGrad
  have henergy_eq :
      volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) =
        cubeAverage R (scalarVariationEnergyIntegrand a w) :=
    volumeAverage_cubeSet_eq_cubeAverage R (scalarVariationEnergyIntegrand a w)
  calc
    vecNormSq (cubeAverageVec R (fun x => w.toH1.grad x)) = vecNormSq avgGrad := by
      rw [havg_eq]
    _ ≤
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) a) *
          vecDot avgGrad (matVecMul (sigmaStarCoarse (cubeSet R) a) avgGrad) := hgrad
    _ ≤
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) a) *
          volumeAverage (cubeSet R) (scalarVariationEnergyIntegrand a w) := by
            exact mul_le_mul_of_nonneg_left henergy
              (Book.Ch02.matrixNorm_nonneg (sigmaStarInvCoarse (cubeSet R) a))
    _ =
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) a) *
          cubeAverage R (scalarVariationEnergyIntegrand a w) := by
          rw [henergy_eq]

/--
Gradient coarse-square estimate with the deterministic open-cube coarse
witnesses packaged as `OpenCubeDeterministicCoarseData`.
-/
theorem cubeAverageGradient_le_coarseSigmaStarInvBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hData : OpenCubeDeterministicCoarseData R a)
    (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => w.toH1.grad x)) ≤
      coarseSigmaStarInvBlockNorm R a * cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    cubeAverageGradient_le_coarseSigmaStarInvBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEll hA hS hK hSigma hdet w

theorem cubeAverageGradient_le_matrixNorm_sigmaStarInv_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (hData : OpenCubeDeterministicCoarseData R a)
    (w : AHarmonicFunction a (cubeSet R)) :
    vecNormSq (cubeAverageVec R (fun x => w.toH1.grad x)) ≤
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) a) *
        cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact
    cubeAverageGradient_le_matrixNorm_sigmaStarInv_mul_energyAverage_of_isEllipticFieldOn_of_openCubeDeterministicCoarseData
      (R := R) (a := a) hEll hA hS hK hSigma hdet w

theorem cubeAverageGradientEnergyControl_of_aHarmonicFunction {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    CubeAverageGradientEnergyControl Q a
      (fun x => u.toH1.grad x)
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  intro j R hR
  have hEllR :
      IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hj : Q.scale - (j : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hj]
    simpa using hR
  have hDataR : OpenCubeDeterministicCoarseData R a := hData _ hj R hRscale
  let w : AHarmonicFunction a (cubeSet R) := u.restrictToSubcube hEll hR
  have hlocal :=
    cubeAverageGradient_le_coarseSigmaStarInvBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
      (R := R) (a := a) hEllR hDataR w
  have henergy_eq :
      cubeAverage R (scalarVariationEnergyIntegrand a w) =
        cubeAverage R
          (fun x => vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
    apply cubeAverage_eq_of_eq_on_cubeSet
    intro x hx
    simp [w, scalarVariationEnergyIntegrand]
  rw [henergy_eq] at hlocal
  simpa [w] using! hlocal

theorem cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q))
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    CubeAverageGradientEnergyControl Q a
      (fun x => u.toH1.grad x)
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  exact
    cubeAverageGradientEnergyControl_of_aHarmonicFunction
      (Q := Q) (a := a) hEll u
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q))
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    CubeAverageGradientEnergyControl Q a
      (fun x => u.toH1.grad x)
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  exact
    cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) hEll u
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)

theorem mem_descendantsAtScale_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
  have hj : Q.scale - (j : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  rw [descendantsAtScale_eq_descendantsAtDepth Q hj]
  simpa using hR

theorem cubeAverageFluxEnergyControl_of_aHarmonicFunction
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q))
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    CubeAverageFluxEnergyControl Q a
      (fun x => matVecMul (a x) (u.toH1.grad x))
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  intro j R hR
  have hEllR :
      IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  have hj : Q.scale - (j : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le j)
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
    exact mem_descendantsAtScale_of_mem_descendantsAtDepth hR
  have hDataR : OpenCubeDeterministicCoarseData R a := hData _ hj R hRscale
  let w : AHarmonicFunction a (cubeSet R) := u.restrictToSubcube hEll hR
  have hlocal :=
    cubeAverageFlux_le_coarseBBlockNorm_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
      (R := R) (a := a) hEllR hDataR w
  have hflux_eq :
      cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x)) =
        cubeAverageVec R (fun x => matVecMul (a x) (u.toH1.grad x)) := by
    apply cubeAverageVec_eq_of_eq_on_cubeSet
    intro x hx
    simp [w]
  have henergy_eq :
      cubeAverage R (scalarVariationEnergyIntegrand a w) =
        cubeAverage R
          (fun x => vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
    apply cubeAverage_eq_of_eq_on_cubeSet
    intro x hx
    simp [w, scalarVariationEnergyIntegrand]
  rw [hflux_eq, henergy_eq] at hlocal
  simpa [scalarVariationEnergyIntegrand] using hlocal

theorem cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeDescendantEllipticRecoveryFamily
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q))
    (hRec : OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam)) :
    CubeAverageFluxEnergyControl Q a
      (fun x => matVecMul (a x) (u.toH1.grad x))
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  exact
    cubeAverageFluxEnergyControl_of_aHarmonicFunction
      (Q := Q) (a := a) hEll u
      (openCubeDescendantDeterministicCoarseData_of_recoveryFamily hRec)

theorem cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q))
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    CubeAverageFluxEnergyControl Q a
      (fun x => matVecMul (a x) (u.toH1.grad x))
      (fun x => scalarVariationEnergyIntegrand a u x) := by
  exact
    cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeDescendantEllipticRecoveryFamily
      (Q := Q) (a := a) hEll u
      (openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
        (Q := Q) (a := a) hEll hOrigin)


theorem rpow_neg_s_nat_eq_inv_geometricDiscount_mul_geometricWeight
    {s : ℝ} (hs : 0 < s) (j : ℕ) :
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) =
      (geometricDiscount s 1)⁻¹ * geometricWeight s 1 j := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hdisc_ne : geometricDiscount s 1 ≠ 0 := (geometricDiscount_pos hs1).ne'
  calc
    Real.rpow (3 : ℝ) (-s * (j : ℝ)) =
        ((geometricDiscount s 1)⁻¹ * geometricDiscount s 1) *
          Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
          rw [inv_mul_cancel₀ hdisc_ne, one_mul]
    _ = (geometricDiscount s 1)⁻¹ *
          (geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (j : ℝ))) := by
          ring
    _ = (geometricDiscount s 1)⁻¹ * geometricWeight s 1 j := by
          rw [geometricWeight_one_eq]

theorem mul_sqrt_mul_eq_mul_rpow_half_mul_sqrt {a b c : ℝ}
    (ha : 0 ≤ a) :
    c * Real.sqrt (a * b) = c * Real.rpow a (1 / 2 : ℝ) * Real.sqrt b := by
  rw [Real.sqrt_mul ha, Real.sqrt_eq_rpow]
  ring_nf
  ac_rfl



end

end Homogenization
