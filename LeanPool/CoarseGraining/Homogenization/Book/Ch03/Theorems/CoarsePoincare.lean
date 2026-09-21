/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarsePoincare.Infinity
import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Existence
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.QTwo
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-! # Coarse Poincare -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.1.1: Coarse-grained Poincare inequality

This file contains the public note-facing coarse Poincare theorem package.
Helper estimates live in the `CoarsePoincare/` submodules.

## Audit tag

Claim: prove and package the Book-facing coarse Poincare estimate for solution
gradients and energy density on triadic cubes.

Downstream target: Chapter 3 public theorem aggregation and later
inhomogeneous estimates.  This file should keep one `CoarsePoincareTheory`
surface; helper estimates belong in the `CoarsePoincare/` submodules.
-/

noncomputable section

open scoped BigOperators

/-- Gradient part of the note-facing coarse-grained Poincare theorem.

The proved API is uniform for every `s > 0`, and therefore strengthens the
ABK26/source range `0 < s ≤ 1`; it is not presented as a literal identity of
ranges.  In particular, admissible `q` includes the endpoint `s = 1`, `q = 2`.
-/
theorem coarsePoincareGradient_negativeBesov_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {q : Ch02.MultiscaleExponent} (u : CubeSolution Q a)
    (hs : 0 < s) (hq : q.IsAdmissible) :
    scaleNormalizedNegativeBesovVectorNorm Q s q
        (solutionGradientField u) ≤
      coarsePoincareGradientRHS Q a s q u := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let aQ : Ch02.CoeffOn U := a.coeffOn Q
  let ap : Ch02.CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U aQ
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField U aQ
  have haeeq_ap_a : Ch02.CoeffOn.AEEq ap aQ := by
    simpa [ap] using Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U aQ
  have haeeq_a_ap : Ch02.CoeffOn.AEEq aQ ap := haeeq_ap_a.symm
  let uPw : Ch02.Solution U ap := Ch02.Solution.ofAEEq haeeq_a_ap u
  let uOpen : AHarmonicFunction A (openCubeSet Q) := by
    simpa [U, ap, A] using! uPw
  let uCube : AHarmonicFunction A (cubeSet Q) := uOpen.toCubeSet
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand A uCube x
  have hEll : IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet Q) A := by
    simpa [U, aQ, A] using pointwiseCoeffField_isEllipticFieldOn_cubeSet Q aQ
  have hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) aQ.lam aQ.Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d)
      (lam := aQ.lam) (Lam := aQ.Lam)
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    simpa [energy] using
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) A hEll uCube
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := by
    simpa [energy] using
      ResponseLinearIntegrabilityData.energy
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) uCube
  have hgrad :
      Homogenization.CubeAverageGradientEnergyControl Q A
        (fun x => uCube.toH1.grad x) energy := by
    simpa [energy] using
      cubeAverageGradientEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := A) hEll uCube hOrigin
  have hgradient_local_public :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R (fun x => uCube.toH1.grad x)) ≤
          Ch02.coarseSigmaStarInvMatrixNorm R a * cubeAverage R energy := by
    intro j R hR
    have hj : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hj]
      simpa using hR
    have hEllR :
        IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet R) A :=
      hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hData :
        OpenCubeDescendantDeterministicCoarseData Q A := by
      simpa [A, U, aQ] using
        Ch02.pointwiseCoeffField_openCube_descendant_data Q aQ
    have hDataR : OpenCubeDeterministicCoarseData R A :=
      hData _ hj R hRscale
    let w : AHarmonicFunction A (cubeSet R) := uCube.restrictToSubcube hEll hR
    have hraw :=
      cubeAverageGradient_le_matrixNorm_sigmaStarInv_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
        (R := R) (a := A) hEllR hDataR w
    have henergy_R :
        cubeAverage R (scalarVariationEnergyIntegrand A w) =
          cubeAverage R energy := by
      apply cubeAverage_eq_of_eq_on_cubeSet
      intro x hx
      simp [w, energy, scalarVariationEnergyIntegrand]
    have hnorm_R :
        Ch02.matrixNorm (sigmaStarInvCoarse (cubeSet R) A) =
          Ch02.coarseSigmaStarInvMatrixNorm R a := by
      simpa [A, U, aQ] using
        (Ch02.coarseSigmaStarInvMatrixNorm_eq_matrixNorm_sigmaStarInv_pointwiseCoeffField_of_mem_descendantsAtScale
          (a := a) (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) hj hRscale).symm
    rw [henergy_R, hnorm_R] at hraw
    simpa [w] using hraw
  have hgradient_depth :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q (fun x => uCube.toH1.grad x) n ≤
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
            cubeAverage Q energy := by
    intro n
    exact negativeBesovVectorDepthAverage_le_publicSigmaStarInvEnergy
      (Q := Q) a (fun x => uCube.toH1.grad x) energy
      henergy_nonneg henergy_int hgradient_local_public n
  have henergy_eq :
      cubeAverage Q energy =
        Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u := by
    have henergy_fun :
        energy = Ch02.variationEnergyIntegrand U ap uPw := by
      funext x
      simp [energy, scalarVariationEnergyIntegrand, Ch02.variationEnergyIntegrand,
        uCube, uOpen, uPw, U, ap, A, Internal.Ch02.BookCh02.pointwiseCoeffOn]
      rfl
    have hcube_pw :
        cubeAverage Q energy = Ch02.variationEnergyValue U ap uPw := by
      calc
        cubeAverage Q energy = volumeAverage (cubeSet Q) energy := by
          rw [volumeAverage_cubeSet_eq_cubeAverage]
        _ = volumeAverage (openCubeSet Q) energy :=
          ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q energy
        _ = Ch02.average U (Ch02.variationEnergyIntegrand U ap uPw) := by
          rw [henergy_fun]
          exact (Internal.Ch02.book_average_eq_volumeAverage U
            (Ch02.variationEnergyIntegrand U ap uPw)).symm
    calc
      cubeAverage Q energy = Ch02.variationEnergyValue U ap uPw := hcube_pw
      _ = Ch02.variationEnergyValue U aQ u := by
        simpa [uPw] using Ch02.variationEnergyValue_ofAEEq haeeq_a_ap u
      _ = Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u := by
        rfl
  have hgrad_ae :
      (fun x => uCube.toH1.grad x)
        =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] solutionGradientField u := by
    exact Filter.Eventually.of_forall fun x => by
      simp [solutionGradientField, uCube, uOpen, uPw, U, ap, A]
      rfl
  cases q with
  | finite q =>
      have hq' : 1 ≤ q := by simpa using hq
      have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq'
      have hraw :
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
              (fun x => uCube.toH1.grad x) ≤
            poincareDiscountFactor s (.finite q) *
              poincareLowerEllipticityFactor Q a s (.finite q) *
                Real.sqrt (cubeAverage Q energy) :=
        finite_gradient_norm_le_of_cubeAverageEnergyControl
          Q a s q hs hq' (fun x => uCube.toH1.grad x) energy
          henergy_nonneg hgradient_depth
          (summable_public_sigmaStar_series Q a hs hqpos)
          (tsum_public_sigmaStar_series_eq_lambdaSq Q a hs hqpos)
      have hnorm_eq :
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
              (fun x => uCube.toH1.grad x) =
            scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
              (solutionGradientField u) :=
        scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet s (.finite q) hgrad_ae
      calc
        scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
            (solutionGradientField u)
            =
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
            (fun x => uCube.toH1.grad x) := hnorm_eq.symm
        _ ≤
          poincareDiscountFactor s (.finite q) *
            poincareLowerEllipticityFactor Q a s (.finite q) *
              Real.sqrt (cubeAverage Q energy) := hraw
        _ = coarsePoincareGradientRHS Q a s (.finite q) u := by
          simp [coarsePoincareGradientRHS, solutionEnergyNorm, henergy_eq]
  | infinity =>
      have hraw :
          scaleNormalizedNegativeBesovVectorNorm Q s .infinity
              (fun x => uCube.toH1.grad x) ≤
            poincareDiscountFactor s .infinity *
              poincareLowerEllipticityFactor Q a s .infinity *
                Real.sqrt (cubeAverage Q energy) :=
        infinity_gradient_norm_le_of_cubeAverageEnergyControl
          Q a s hs (fun x => uCube.toH1.grad x) energy
          henergy_nonneg hgradient_depth
      have hnorm_eq :
          scaleNormalizedNegativeBesovVectorNorm Q s .infinity
              (fun x => uCube.toH1.grad x) =
            scaleNormalizedNegativeBesovVectorNorm Q s .infinity
              (solutionGradientField u) :=
        scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet s .infinity hgrad_ae
      calc
        scaleNormalizedNegativeBesovVectorNorm Q s .infinity
            (solutionGradientField u)
            =
          scaleNormalizedNegativeBesovVectorNorm Q s .infinity
            (fun x => uCube.toH1.grad x) := hnorm_eq.symm
        _ ≤
          poincareDiscountFactor s .infinity *
            poincareLowerEllipticityFactor Q a s .infinity *
              Real.sqrt (cubeAverage Q energy) := hraw
        _ = coarsePoincareGradientRHS Q a s .infinity u := by
          simp [coarsePoincareGradientRHS, solutionEnergyNorm, henergy_eq]

/-- Flux part of the note-facing coarse-grained Poincare theorem.

The proved API is uniform for every `s > 0`, and therefore strengthens the
ABK26/source range `0 < s ≤ 1`; it is not presented as a literal identity of
ranges.  In particular, admissible `q` includes the endpoint `s = 1`, `q = 2`.
-/
theorem coarsePoincareFlux_negativeBesov_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} {q : Ch02.MultiscaleExponent} (u : CubeSolution Q a)
    (hs : 0 < s) (hq : q.IsAdmissible) :
    scaleNormalizedNegativeBesovVectorNorm Q s q
        (solutionFluxField Q a u) ≤
      coarsePoincareFluxRHS Q a s q u := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let aQ : Ch02.CoeffOn U := a.coeffOn Q
  let ap : Ch02.CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U aQ
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField U aQ
  have haeeq_ap_a : Ch02.CoeffOn.AEEq ap aQ := by
    simpa [ap] using Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U aQ
  have haeeq_a_ap : Ch02.CoeffOn.AEEq aQ ap := haeeq_ap_a.symm
  let uPw : Ch02.Solution U ap := Ch02.Solution.ofAEEq haeeq_a_ap u
  let uOpen : AHarmonicFunction A (openCubeSet Q) := by
    simpa [U, ap, A] using! uPw
  let uCube : AHarmonicFunction A (cubeSet Q) := uOpen.toCubeSet
  let oldFlux : Vec d → Vec d := fun x => matVecMul (A x) (uCube.toH1.grad x)
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand A uCube x
  have hEll : IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet Q) A := by
    simpa [U, aQ, A] using pointwiseCoeffField_isEllipticFieldOn_cubeSet Q aQ
  have hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) aQ.lam aQ.Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d)
      (lam := aQ.lam) (Lam := aQ.Lam)
  have henergy_nonneg : ∀ x ∈ cubeSet Q, 0 ≤ energy x := by
    simpa [energy] using
      scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) A hEll uCube
  have henergy_int :
      MeasureTheory.IntegrableOn energy (cubeSet Q) MeasureTheory.volume := by
    simpa [energy] using
      ResponseLinearIntegrabilityData.energy
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) uCube
  have hflux :
      Homogenization.CubeAverageFluxEnergyControl Q A oldFlux energy := by
    simpa [oldFlux, energy] using
      cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := A) hEll uCube hOrigin
  have hflux_local_public :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        vecNormSq (cubeAverageVec R oldFlux) ≤
          Ch02.coarseBMatrixNorm R a * cubeAverage R energy := by
    intro j R hR
    have hj : Q.scale - (j : ℤ) ≤ Q.scale :=
      sub_le_self _ (by exact_mod_cast Nat.zero_le j)
    have hRscale : R ∈ descendantsAtScale Q (Q.scale - (j : ℤ)) := by
      rw [descendantsAtScale_eq_descendantsAtDepth Q hj]
      simpa using hR
    have hEllR :
        IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet R) A :=
      hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hData :
        OpenCubeDescendantDeterministicCoarseData Q A := by
      simpa [A, U, aQ] using
        Ch02.pointwiseCoeffField_openCube_descendant_data Q aQ
    have hDataR : OpenCubeDeterministicCoarseData R A :=
      hData _ hj R hRscale
    let w : AHarmonicFunction A (cubeSet R) := uCube.restrictToSubcube hEll hR
    have hraw :=
      cubeAverageFlux_le_matrixNorm_bCoarse_mul_energyAverage_of_isEllipticFieldOn_of_deterministicCoarseData
        (R := R) (a := A) hEllR hDataR w
    have hflux_R :
        cubeAverageVec R (fun x => matVecMul (A x) (w.toH1.grad x)) =
          cubeAverageVec R oldFlux := by
      apply cubeAverageVec_eq_of_eq_on_cubeSet
      intro x hx
      simp [w, oldFlux]
    have henergy_R :
        cubeAverage R (scalarVariationEnergyIntegrand A w) =
          cubeAverage R energy := by
      apply cubeAverage_eq_of_eq_on_cubeSet
      intro x hx
      simp [w, energy, scalarVariationEnergyIntegrand]
    have hnorm_R :
        Ch02.matrixNorm
            (Homogenization.bCoarse
              (Homogenization.sigmaCoarse (cubeSet R) A)
              (Homogenization.sigmaStarCoarse (cubeSet R) A)
              (Homogenization.kappaCoarse (cubeSet R) A)) =
          Ch02.coarseBMatrixNorm R a := by
      simpa [A, U, aQ] using
        (Ch02.coarseBMatrixNorm_eq_matrixNorm_bCoarse_pointwiseCoeffField_of_mem_descendantsAtScale
          (a := a) (Q := Q) (R := R) (k := Q.scale - (j : ℤ)) hj hRscale).symm
    rw [hflux_R, henergy_R, hnorm_R] at hraw
    simpa using hraw
  have hflux_depth :
      ∀ n : ℕ,
        negativeBesovVectorDepthAverage Q oldFlux n ≤
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) a *
            cubeAverage Q energy := by
    intro n
    exact negativeBesovVectorDepthAverage_le_publicBEnergy
      (Q := Q) a oldFlux energy henergy_nonneg henergy_int hflux_local_public n
  have henergy_eq :
      cubeAverage Q energy =
        Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u := by
    have henergy_fun :
        energy = Ch02.variationEnergyIntegrand U ap uPw := by
      funext x
      simp [energy, scalarVariationEnergyIntegrand, Ch02.variationEnergyIntegrand,
        uCube, uOpen, uPw, U, ap, A, Internal.Ch02.BookCh02.pointwiseCoeffOn]
      rfl
    have hcube_pw :
        cubeAverage Q energy = Ch02.variationEnergyValue U ap uPw := by
      calc
        cubeAverage Q energy = volumeAverage (cubeSet Q) energy := by
          rw [volumeAverage_cubeSet_eq_cubeAverage]
        _ = volumeAverage (openCubeSet Q) energy :=
          ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q energy
        _ = Ch02.average U (Ch02.variationEnergyIntegrand U ap uPw) := by
          rw [henergy_fun]
          exact (Internal.Ch02.book_average_eq_volumeAverage U
            (Ch02.variationEnergyIntegrand U ap uPw)).symm
    calc
      cubeAverage Q energy = Ch02.variationEnergyValue U ap uPw := hcube_pw
      _ = Ch02.variationEnergyValue U aQ u := by
        simpa [uPw] using Ch02.variationEnergyValue_ofAEEq haeeq_a_ap u
      _ = Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u := by
        rfl
  have hA_ae_open :
      A =ᵐ[volumeMeasureOn (openCubeSet Q)] (a.coeffOn Q).toCoeffField := by
    simpa [A, U, aQ, volumeMeasureOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U aQ
  have hA_ae_cube :
      A =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] (a.coeffOn Q).toCoeffField := by
    simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hA_ae_open
  have hflux_ae :
      oldFlux =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] solutionFluxField Q a u := by
    exact hA_ae_cube.mono fun x hx => by
      simp [oldFlux, solutionFluxField, uCube, uOpen, uPw, U, ap, A, hx]
      rfl
  cases q with
  | finite q =>
      have hq' : 1 ≤ q := by simpa using hq
      have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq'
      have hraw :
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) oldFlux ≤
            poincareDiscountFactor s (.finite q) *
              poincareUpperEllipticityFactor Q a s (.finite q) *
                Real.sqrt (cubeAverage Q energy) :=
        finite_flux_norm_le_of_cubeAverageEnergyControl
          Q a s q hs hq' oldFlux energy
          henergy_nonneg hflux_depth
          (summable_public_B_series Q a hs hqpos)
          (tsum_public_B_series_eq_LambdaSq Q a hs hqpos)
      have hnorm_eq :
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) oldFlux =
            scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
              (solutionFluxField Q a u) :=
        scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet s (.finite q) hflux_ae
      calc
        scaleNormalizedNegativeBesovVectorNorm Q s (.finite q)
            (solutionFluxField Q a u)
            =
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite q) oldFlux := hnorm_eq.symm
        _ ≤
          poincareDiscountFactor s (.finite q) *
            poincareUpperEllipticityFactor Q a s (.finite q) *
              Real.sqrt (cubeAverage Q energy) := hraw
        _ = coarsePoincareFluxRHS Q a s (.finite q) u := by
          simp [coarsePoincareFluxRHS, solutionEnergyNorm, henergy_eq]
  | infinity =>
      have hraw :
          scaleNormalizedNegativeBesovVectorNorm Q s .infinity oldFlux ≤
            poincareDiscountFactor s .infinity *
              poincareUpperEllipticityFactor Q a s .infinity *
                Real.sqrt (cubeAverage Q energy) :=
        infinity_flux_norm_le_of_cubeAverageEnergyControl
          Q a s hs oldFlux energy
          henergy_nonneg hflux_depth
      have hnorm_eq :
          scaleNormalizedNegativeBesovVectorNorm Q s .infinity oldFlux =
            scaleNormalizedNegativeBesovVectorNorm Q s .infinity
              (solutionFluxField Q a u) :=
        scaleNormalizedNegativeBesovVectorNorm_eq_of_ae_eq_on_cubeSet s .infinity hflux_ae
      calc
        scaleNormalizedNegativeBesovVectorNorm Q s .infinity
            (solutionFluxField Q a u)
            =
          scaleNormalizedNegativeBesovVectorNorm Q s .infinity oldFlux := hnorm_eq.symm
        _ ≤
          poincareDiscountFactor s .infinity *
            poincareUpperEllipticityFactor Q a s .infinity *
              Real.sqrt (cubeAverage Q energy) := hraw
        _ = coarsePoincareFluxRHS Q a s .infinity u := by
          simp [coarsePoincareFluxRHS, solutionEnergyNorm, henergy_eq]

/-- Public theorem package for the gradient and flux coarse-grained Poincare
inequalities.

Its proved API is uniform for every `s > 0`, hence strengthens the ABK26/source
range `0 < s ≤ 1` without claiming literal identity of ranges.  Admissible `q`
includes the endpoint `s = 1`, `q = 2`.
-/
structure CoarsePoincareTheory {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) : Prop where
  gradient_negativeBesov_le :
    ∀ {s : ℝ} {q : Ch02.MultiscaleExponent} (u : CubeSolution Q a),
      0 < s → q.IsAdmissible →
        scaleNormalizedNegativeBesovVectorNorm Q s q
            (solutionGradientField u) ≤
          coarsePoincareGradientRHS Q a s q u
  flux_negativeBesov_le :
    ∀ {s : ℝ} {q : Ch02.MultiscaleExponent} (u : CubeSolution Q a),
      0 < s → q.IsAdmissible →
        scaleNormalizedNegativeBesovVectorNorm Q s q
            (solutionFluxField Q a u) ≤
          coarsePoincareFluxRHS Q a s q u

/-- Fully proved public coarse-grained Poincare theorem. -/
theorem coarsePoincareTheory {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d) :
    CoarsePoincareTheory Q a := by
  refine ⟨?_, ?_⟩
  · intro s q u hs hq
    exact coarsePoincareGradient_negativeBesov_le (Q := Q) (a := a) (u := u)
      hs hq
  · intro s q u hs hq
    exact coarsePoincareFlux_negativeBesov_le (Q := Q) (a := a) (u := u)
      hs hq

end

end Ch03
end Book
end Homogenization
