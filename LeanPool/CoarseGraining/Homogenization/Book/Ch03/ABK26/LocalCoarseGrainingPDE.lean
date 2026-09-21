/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.LocalCoarseGrainingDefinitions
import LeanPool.CoarseGraining.Homogenization.Deterministic.HomogenizationBlackBoxes.Duality
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfacesComponentwise
import LeanPool.CoarseGraining.Homogenization.PDE.EnergyIdentities
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-!
# Local coarse-graining PDE bridges

This module transports the source-facing weak equation and finite-`p` forcing
assumption to the internal carriers used by local coarse-graining estimates.
The public statements retain `CoeffOn`; pointwise coefficient representatives
are confined to the private bridge to the legacy weak-solution predicate.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem setIntegral_vecDot_extendByZeroToOpenSuperset {d : ℕ}
    {U V : Set (Vec d)} (hU : MeasurableSet U) (hV : IsOpen V) (hUV : U ⊆ V)
    (F : Vec d → Vec d) (phi : H10Function U) :
    ∫ x in V, vecDot (F x)
        ((phi.extendByZeroToOpenSuperset hU hV hUV).grad x) ∂volume =
      ∫ x in U, vecDot (F x) (phi.grad x) ∂volume := by
  let phiV : H10Function V := phi.extendByZeroToOpenSuperset hU hV hUV
  have hgrad : phiV.grad = phi.zeroExtensionGrad := by
    simpa only [phiV] using
      H10Function.extendByZeroToOpenSuperset_grad phi hU hV hUV
  have hindicator :
      (fun x => vecDot (F x) (phiV.grad x)) =
        U.indicator (fun x => vecDot (F x) (phi.grad x)) := by
    funext x
    rw [hgrad]
    by_cases hx : x ∈ U
    · simp only [H10Function.zeroExtensionGrad_apply_of_mem _ hx,
        Set.indicator_of_mem hx]
    · simp only [H10Function.zeroExtensionGrad_apply_of_not_mem _ hx,
        Set.indicator_of_notMem hx, vecDot_zero_right]
  rw [show (phi.extendByZeroToOpenSuperset hU hV hUV).grad = phiV.grad by rfl,
    hindicator, MeasureTheory.integral_indicator hU, Measure.restrict_restrict hU,
    Set.inter_eq_left.mpr hUV]

/-- The source weak equation restricts to every descendant by zero-extending
the descendant test function. -/
theorem IsForcedEquation.restrictToDescendant {d : ℕ}
    {Q R : TriadicCube d} {n : ℤ}
    (hn : n ≤ Q.scale) (hR : R ∈ descendantsAtScale Q n)
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsForcedEquation Q a u g) :
    IsForcedEquation R
      (a.restrictToSubcube (openCubeSet_subset_of_mem_descendantsAtScale hn hR))
      (restrictH1ToSubcube u
        (openCubeSet_subset_of_mem_descendantsAtScale hn hR)) g := by
  let hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hn hR
  intro phi
  let phiQ : H10Function (openCubeSet Q) :=
    phi.extendByZeroToOpenSuperset (measurableSet_openCubeSet R)
      (isOpen_openCubeSet Q) hRQ
  have hflux := setIntegral_vecDot_extendByZeroToOpenSuperset
    (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ
    (fun x => matVecMul (a.toCoeffField x) (u.grad x)) phi
  have hforcing := setIntegral_vecDot_extendByZeroToOpenSuperset
    (measurableSet_openCubeSet R) (isOpen_openCubeSet Q) hRQ g phi
  calc
    ∫ x in openCubeSet R,
        vecDot
          (matVecMul
            ((a.restrictToSubcube hRQ).toCoeffField x)
            ((restrictH1ToSubcube u hRQ).grad x))
          (phi.grad x) ∂volume =
        ∫ x in openCubeSet Q,
          vecDot (matVecMul (a.toCoeffField x) (u.grad x))
            (phiQ.grad x) ∂volume := by
          simpa only [Book.Ch02.CoeffOn.restrictToSubcube_toCoeffField,
            restrictH1ToSubcube_grad, phiQ] using hflux.symm
    _ = -(∫ x in openCubeSet Q, vecDot (g x) (phiQ.grad x) ∂volume) := h phiQ
    _ = -(∫ x in openCubeSet R, vecDot (g x) (phi.grad x) ∂volume) := by
      rw [hforcing]

/-- Finite-`p` source forcing is `L²` on every descendant whenever `p ≥ 2`. -/
theorem MemCubeEuclideanFullWsp.memLpTwoOnDescendant {d : ℕ}
    {Q R : TriadicCube d} {n : ℤ} {s : FractionalOrder}
    {p : FiniteLpExponent} {g : Vec d → Vec d}
    (hn : n ≤ Q.scale) (hR : R ∈ descendantsAtScale Q n)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent)
    (h : MemCubeEuclideanFullWsp Q s p g) :
    MemLp (fun x => HilbertVec.ofVec (g x)) 2 (normalizedCubeMeasure R) := by
  have hRdepth : R ∈ descendantsAtDepth Q (Int.toNat (Q.scale - n)) := by
    rw [← descendantsAtScale_eq_descendantsAtDepth Q hn]
    exact hR
  exact (memLp_on_descendant_of_memLp_generic hRdepth h.1).mono_exponent hp

private theorem isH1DirichletRhsWeakSolutionOn_pointwiseCoeffOn_neg_of_isForcedEquation
    {d : ℕ} {Q : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsForcedEquation Q a u g) :
    IsH1DirichletRhsWeakSolutionOn
      (Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a).toCoeffField
      (openCubeSet Q) u (fun x => -g x) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain Q) a
  intro phi
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (b.toCoeffField x) (u.grad x)) (phi.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (phi.grad x) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hba] with x hx
          simp only [hx]
    _ = -(∫ x in openCubeSet Q, vecDot (g x) (phi.grad x) ∂volume) := h phi
    _ = ∫ x in openCubeSet Q, vecDot (-g x) (phi.grad x) ∂volume := by
      rw [← MeasureTheory.integral_neg]
      congr with x
      exact (vecDot_neg_left (g x) (phi.grad x)).symm

/-- The source negative-sign weak equation is the legacy weak-solution
carrier with datum `-g`. -/
theorem IsForcedEquation.toIsH1DirichletRhsWeakSolutionOnNeg {d : ℕ}
    {Q : TriadicCube d}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)}
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (h : IsForcedEquation Q a u g) :
    IsH1DirichletRhsWeakSolutionOn a.toCoeffField (openCubeSet Q) u
      (fun x => -g x) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain Q) a
  have hb := isH1DirichletRhsWeakSolutionOn_pointwiseCoeffOn_neg_of_isForcedEquation h
  intro phi
  calc
    ∫ x in openCubeSet Q,
        vecDot (matVecMul (a.toCoeffField x) (u.grad x)) (phi.grad x) ∂volume =
      ∫ x in openCubeSet Q,
        vecDot (matVecMul (b.toCoeffField x) (u.grad x)) (phi.grad x) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hba] with x hx
          simp only [hx]
    _ = ∫ x in openCubeSet Q, vecDot (-g x) (phi.grad x) ∂volume := hb phi

/-- The local symmetric energy is exactly the old coefficient-energy density
integrated against the normalized cube measure. -/
theorem localSymmetricEnergyENorm_eq_coefficientEnergyDensity {d : ℕ}
    (R : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    localSymmetricEnergyENorm R a u =
      (∫⁻ x, ENNReal.ofReal
        (coefficientEnergyDensity a.toCoeffField u.grad x)
        ∂normalizedCubeMeasure R) ^ (1 / 2 : ℝ) := rfl

private theorem integrable_coefficientEnergyDensity_normalizedCubeMeasure {d : ℕ}
    (R : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    Integrable (coefficientEnergyDensity a.toCoeffField u.grad)
      (normalizedCubeMeasure R) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain R) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet R) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Book.Ch02.cubeDomain R) a
  have hB : IntegrableOn (coefficientEnergyDensity b.toCoeffField u.grad)
      (openCubeSet R) :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain R) a
  have hA : IntegrableOn (coefficientEnergyDensity a.toCoeffField u.grad)
      (openCubeSet R) := by
    apply hB.congr
    filter_upwards [hba] with x hx
    change vecDot (u.grad x)
        (matVecMul (symmPart (b.toCoeffField x)) (u.grad x)) =
      vecDot (u.grad x)
        (matVecMul (symmPart (a.toCoeffField x)) (u.grad x))
    rw [hx]
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
    hA.smul_measure ENNReal.ofReal_ne_top

private theorem ae_nonneg_coefficientEnergyDensity_normalizedCubeMeasure {d : ℕ}
    (R : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    ∀ᵐ x ∂normalizedCubeMeasure R,
      0 ≤ coefficientEnergyDensity a.toCoeffField u.grad x := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain R) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet R) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Book.Ch02.cubeDomain R) a
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet R)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain R) a
  have hnonneg : ∀ᵐ x ∂volumeMeasureOn (openCubeSet R),
      0 ≤ coefficientEnergyDensity a.toCoeffField u.grad x := by
    filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R), hba]
      with x hxR hxa
    change 0 ≤ vecDot (u.grad x)
      (matVecMul (symmPart (a.toCoeffField x)) (u.grad x))
    rw [← hxa]
    exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll u.grad x hxR
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
    MeasureTheory.Measure.ae_smul_measure hnonneg (ENNReal.ofReal ((cubeVolume R)⁻¹))

/-- The local symmetric energy is the square-root energy associated with the
legacy normalized cube average. -/
theorem localSymmetricEnergyENorm_eq_ofReal_cubeAverage_coefficientEnergyDensity
    {d : ℕ} (R : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    localSymmetricEnergyENorm R a u =
      (ENNReal.ofReal
        (cubeAverage R (coefficientEnergyDensity a.toCoeffField u.grad))) ^
        (1 / 2 : ℝ) := by
  rw [localSymmetricEnergyENorm_eq_coefficientEnergyDensity]
  congr 1
  symm
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_coefficientEnergyDensity_normalizedCubeMeasure R a u)
    (ae_nonneg_coefficientEnergyDensity_normalizedCubeMeasure R a u)

/-- The normalized local symmetric energy is nonnegative. -/
theorem localSymmetricEnergyENorm_nonneg {d : ℕ}
    (R : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    0 ≤ localSymmetricEnergyENorm R a u := bot_le

/-- The local symmetric energy is finite. -/
theorem localSymmetricEnergyENorm_ne_top {d : ℕ}
    (R : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) :
    localSymmetricEnergyENorm R a u ≠ ⊤ := by
  rw [localSymmetricEnergyENorm_eq_coefficientEnergyDensity]
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  have hnorm_ne_top :
      ∫⁻ x, ‖coefficientEnergyDensity a.toCoeffField u.grad x‖ₑ
        ∂normalizedCubeMeasure R ≠ ⊤ := by
    exact ne_of_lt (MeasureTheory.hasFiniteIntegral_iff_enorm.mp
      (integrable_coefficientEnergyDensity_normalizedCubeMeasure R a u).hasFiniteIntegral)
  exact ne_top_of_le_ne_top
    hnorm_ne_top
    (MeasureTheory.lintegral_ofReal_le_lintegral_enorm _)

end

end ABK26
end Ch03
end Book
end Homogenization
