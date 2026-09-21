/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.ReflectionWeakEquation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCoerciveH1

/-!
# Centered-cube Neumann energy and duality

This file supplies the `q = 2` energy endpoint and the canonical mean-zero
adjoint used by the below-two Neumann Calderón--Zygmund argument.  Coercivity
and solvability are discharged internally from the centered-cube geometry.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume_neumann
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem memVectorL2_openCubeSet_of_cubeEuclideanLpField_two
    {d : ℕ} {Q : TriadicCube d}
    (h : CubeEuclideanLpField Q FiniteLpExponent.two) :
    MemVectorL2 (openCubeSet Q) h.toField := by
  have hnormalized : MemLp (fun x ↦ HilbertVec.ofVec (h.toField x)) 2
      (cubeBoundedMeasurableDomain Q).normalizedVolume := by
    simpa only [FiniteLpExponent.two_exponent,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      h.euclideanMemLp
  have hrestricted : MemLp (fun x ↦ HilbertVec.ofVec (h.toField x)) 2
      (cubeBoundedMeasurableDomain Q).restrictedVolume :=
    ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff 2 _).mp hnormalized
  have hopen : MemLp (fun x ↦ HilbertVec.ofVec (h.toField x)) 2
      (volume.restrict (openCubeSet Q)) := by
    simpa only [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
      using hrestricted
  let T : HilbertVec d →L[ℝ] Vec d :=
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
  simpa only [MemVectorL2, volumeMeasureOn, Function.comp_def,
    HilbertVec.toVec_ofVec, T] using! T.comp_memLp' hopen

private theorem norm_meanZeroGradToHilbertVectorL2_le_sigmaInv_datum
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    {H : Vec d → Vec d} (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hweak : ∀ psi : H1MeanZeroFunction (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (H x) (psi.toH1Function.grad x) ∂volume) :
    ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
      sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hH‖ := by
  let G : HilbertVectorL2 (openCubeSet (originCube d m)) :=
    u.toH1Function.gradToHilbertVectorL2
  let K : HilbertVectorL2 (openCubeSet (originCube d m)) :=
    toHilbertVectorL2OfVecField hH
  have hgrad_integral :
      ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        ‖G‖ ^ 2 := by
    calc
      ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        inner ℝ G G := by
          simpa [G, H1Function.gradToHilbertVectorL2] using
            (inner_toHilbertVectorL2OfVecField_eq_integral
              (U := openCubeSet (originCube d m))
              u.toH1Function.grad_memVectorL2
              u.toH1Function.grad_memVectorL2).symm
      _ = ‖G‖ ^ 2 := real_inner_self_eq_norm_sq G
  have hpair_integral :
      ∫ x in openCubeSet (originCube d m),
          vecDot (H x) (u.toH1Function.grad x) ∂volume = inner ℝ K G := by
    simpa [K, G, H1Function.gradToHilbertVectorL2] using
      (inner_toHilbertVectorL2OfVecField_eq_integral
        (U := openCubeSet (originCube d m)) hH
        u.toH1Function.grad_memVectorL2).symm
  have henergy := hweak u
  rw [hgrad_integral, hpair_integral] at henergy
  have henergy_le : sigma0 * ‖G‖ ^ 2 ≤ ‖K‖ * ‖G‖ := by
    calc
      sigma0 * ‖G‖ ^ 2 = -inner ℝ K G := henergy
      _ ≤ |inner ℝ K G| := neg_le_abs _
      _ ≤ ‖K‖ * ‖G‖ := abs_real_inner_le_norm K G
  by_cases hGzero : ‖G‖ = 0
  · rw [hGzero]
    exact mul_nonneg (inv_nonneg.mpr hsigma0.le) (norm_nonneg K)
  · have hGpos : 0 < ‖G‖ := lt_of_le_of_ne (norm_nonneg G) (Ne.symm hGzero)
    have hsigmaG : sigma0 * ‖G‖ ≤ ‖K‖ := by
      apply le_of_mul_le_mul_right _ hGpos
      simpa [pow_two, mul_assoc] using henergy_le
    have hdiv : ‖G‖ ≤ ‖K‖ / sigma0 := by
      apply (le_div_iff₀ hsigma0).2
      simpa [mul_comm] using hsigmaG
    simpa [G, K, div_eq_mul_inv, mul_comm] using hdiv

private theorem centeredCubeNormalized_eLpNorm_meanZeroGrad_le_scaledDatum
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    {H : Vec d → Vec d} (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hweak : ∀ psi : H1MeanZeroFunction (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (H x) (psi.toH1Function.grad x) ∂volume) :
    eLpNorm (hilbertifyVecField u.toH1Function.grad) 2
        (centeredCubeDomain d m).normalizedVolume ≤
      eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
        (centeredCubeDomain d m).normalizedVolume := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hc : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr
    (inv_pos.mpr (cubeVolume_pos (originCube d m))))
  have henergy :=
    norm_meanZeroGradToHilbertVectorL2_le_sigmaInv_datum hsigma0 u hH hweak
  have hraw :
      eLpNorm (hilbertifyVecField u.toH1Function.grad) 2
          (volume.restrict (openCubeSet (originCube d m))) ≤
        eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
          (volume.restrict (openCubeSet (originCube d m))) := by
    rw [eLpNorm_const_smul,
      eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2,
      eLpNorm_hilbertifyVecField_two_eq_ofReal_norm_toHilbertVectorL2 hH]
    rw [← ofReal_norm,
      Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hsigma0.le)]
    exact ENNReal.ofReal_le_ofReal henergy
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume_neumann]
  change eLpNorm (hilbertifyVecField u.toH1Function.grad) 2
      (c • volume.restrict (openCubeSet (originCube d m))) ≤
    eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
      (c • volume.restrict (openCubeSet (originCube d m)))
  rw [eLpNorm_smul_measure_of_ne_zero hc,
    eLpNorm_smul_measure_of_ne_zero hc]
  exact mul_le_mul_right hraw _

/-- The `q = 2` energy estimate for a supplied mean-zero Neumann solution on a
centered cube.  The datum is only the normalized Euclidean `L²` field exposed by
the finite-exponent API. -/
theorem centeredCubeH1MeanZeroScalarDivergence_cz_two
    {d : ℕ} [NeZero d] (m : ℤ) (sigma0 : ℝ)
    (h : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (hsigma0 : 0 < sigma0)
    (hsolution : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x)) :
    (centeredCubeDomain d m).normalizedEuclideanLpENorm
        FiniteLpExponent.two.exponent u.toH1Function.grad ≤
      (ENNReal.ofReal sigma0)⁻¹ *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm
          FiniteLpExponent.two.exponent h.toField := by
  have hH : MemVectorL2 (openCubeSet (originCube d m)) h.toField :=
    memVectorL2_openCubeSet_of_cubeEuclideanLpField_two h
  have hnormalized :=
    centeredCubeNormalized_eLpNorm_meanZeroGrad_le_scaledDatum hsigma0 u hH
      hsolution.scalarMatrix_neg_weak
  rw [eLpNorm_const_smul] at hnormalized
  rw [← ofReal_norm,
    Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
    ENNReal.ofReal_inv_of_pos hsigma0] at hnormalized
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    FiniteLpExponent.two_exponent, euclideanNorm_eq_norm_ofVec,
    eLpNorm_norm, hilbertifyVecField] using! hnormalized

private theorem nonempty_openCubeSet_originCube_neumann (d : ℕ) (m : ℤ) :
    Set.Nonempty (openCubeSet (originCube d m)) := by
  refine ⟨0, ?_⟩
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hpow : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  constructor <;> simp only [Pi.zero_apply] <;> nlinarith

private theorem isEllipticFieldOn_scalarMatrix_centeredCube
    {d : ℕ} {m : ℤ} {sigma0 : ℝ} (hsigma0 : 0 < sigma0) :
    IsEllipticFieldOn sigma0 sigma0 (openCubeSet (originCube d m))
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0) := by
  classical
  constructor
  · apply measurable_pi_iff.2
    intro i
    apply measurable_pi_iff.2
    intro j
    have hpiece : Measurable
        ((openCubeSet (originCube d m)).piecewise
          (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0 i j)
          (fun _ ↦ 0)) :=
      measurable_const.piecewise (measurableSet_openCubeSet _) measurable_const
    simpa only [Set.piecewise] using! hpiece
  · intro x _hx
    exact isEllipticMatrix_scalarMatrix hsigma0

/-- The canonical mean-zero solution of the scalar divergence equation with
datum `-G` on a centered cube. -/
noncomputable def centeredCubeMeanZeroScalarDivergenceSolution
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (G : Vec d → Vec d)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    H1MeanZeroFunction (openCubeSet (originCube d m)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d m)).isFiniteMeasure_restrict_volume
  exact H1MeanZeroFunction.coeffGradientProblemSolution
    (f := fun x ↦ -G x) hG.neg
    (originCubeMeanZeroH1CoerciveEstimate d m)
    (nonempty_openCubeSet_originCube_neumann d m)
    (isEllipticFieldOn_scalarMatrix_centeredCube hsigma0)

/-- The canonical mean-zero adjoint satisfies the packaged weak equation with
the same negative-datum convention as the supplied solution. -/
theorem centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (G : Vec d → Vec d)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m))
      (centeredCubeMeanZeroScalarDivergenceSolution m hsigma0 G hG)
      (fun x ↦ -G x) := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d m)).isFiniteMeasure_restrict_volume
  exact isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
    hG.neg (originCubeMeanZeroH1CoerciveEstimate d m)
    (nonempty_openCubeSet_originCube_neumann d m)
    (isEllipticFieldOn_scalarMatrix_centeredCube hsigma0)

/-- Raw-volume weak equation for the canonical centered Neumann adjoint. -/
theorem centeredCubeMeanZeroScalarDivergenceSolution_weak
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (G : Vec d → Vec d)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G)
    (psi : H1MeanZeroFunction (openCubeSet (originCube d m))) :
    sigma0 * ∫ x in openCubeSet (originCube d m),
        vecDot
          ((centeredCubeMeanZeroScalarDivergenceSolution m hsigma0 G hG).toH1Function.grad x)
          (psi.toH1Function.grad x) ∂volume =
      -∫ x in openCubeSet (originCube d m),
        vecDot (G x) (psi.toH1Function.grad x) ∂volume := by
  exact (centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
    m hsigma0 G hG).scalarMatrix_neg_weak psi

/-- Normalized-volume weak equation for the canonical centered Neumann
adjoint. -/
theorem centeredCubeMeanZeroScalarDivergenceSolution_normalized_weak
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (G : Vec d → Vec d)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G)
    (psi : H1MeanZeroFunction (openCubeSet (originCube d m))) :
    sigma0 * ∫ x,
        vecDot
          ((centeredCubeMeanZeroScalarDivergenceSolution m hsigma0 G hG).toH1Function.grad x)
          (psi.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, vecDot (G x) (psi.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume_neumann,
    integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
  calc
    sigma0 *
        ((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot
              ((centeredCubeMeanZeroScalarDivergenceSolution
                m hsigma0 G hG).toH1Function.grad x)
              (psi.toH1Function.grad x) ∂volume) =
        (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          (sigma0 * ∫ x in openCubeSet (originCube d m),
            vecDot
              ((centeredCubeMeanZeroScalarDivergenceSolution
                m hsigma0 G hG).toH1Function.grad x)
              (psi.toH1Function.grad x) ∂volume) := by ring
    _ = (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          (-∫ x in openCubeSet (originCube d m),
            vecDot (G x) (psi.toH1Function.grad x) ∂volume) := by
          rw [centeredCubeMeanZeroScalarDivergenceSolution_weak]
    _ = -((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot (G x) (psi.toH1Function.grad x) ∂volume) := by ring

/-- Exact normalized cross-pairing identity for two supplied centered Neumann
scalar-divergence solutions. -/
theorem centeredCubeMeanZeroScalarDivergence_cross_pairing
    {d : ℕ} (m : ℤ) {sigma0 : ℝ}
    (u v : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h G : Vec d → Vec d)
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h x))
    (hv : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) v (fun x ↦ -G x)) :
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (h x) (v.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
  have huRaw := hu.scalarMatrix_neg_weak
  have hvRaw := hv.scalarMatrix_neg_weak
  have huNorm : ∀ psi : H1MeanZeroFunction (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (h x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := by
    intro psi
    rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume_neumann,
      integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
    calc
      sigma0 *
          ((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            ∫ x in openCubeSet (originCube d m),
              vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) =
          (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            (sigma0 * ∫ x in openCubeSet (originCube d m),
              vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) := by
            ring
      _ = (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            (-∫ x in openCubeSet (originCube d m),
              vecDot (h x) (psi.toH1Function.grad x) ∂volume) := by
            rw [huRaw psi]
      _ = -((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            ∫ x in openCubeSet (originCube d m),
              vecDot (h x) (psi.toH1Function.grad x) ∂volume) := by ring
  have hvNorm : ∀ psi : H1MeanZeroFunction (openCubeSet (originCube d m)),
      sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        -∫ x, vecDot (G x) (psi.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := by
    intro psi
    rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume_neumann,
      integral_smul_measure, integral_smul_measure, smul_eq_mul, smul_eq_mul]
    calc
      sigma0 *
          ((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            ∫ x in openCubeSet (originCube d m),
              vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) =
          (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            (sigma0 * ∫ x in openCubeSet (originCube d m),
              vecDot (v.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) := by
            ring
      _ = (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            (-∫ x in openCubeSet (originCube d m),
              vecDot (G x) (psi.toH1Function.grad x) ∂volume) := by
            rw [hvRaw psi]
      _ = -((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
            ∫ x in openCubeSet (originCube d m),
              vecDot (G x) (psi.toH1Function.grad x) ∂volume) := by ring
  have hsymm :
      ∫ x, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        ∫ x, vecDot (u.toH1Function.grad x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := by
    apply integral_congr_ae
    filter_upwards with x
    exact vecDot_comm _ _
  have hneg :
      -(∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        -(∫ x, vecDot (h x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) := by
    calc
      -(∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        sigma0 * ∫ x, vecDot (v.toH1Function.grad x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := (hvNorm u).symm
      _ = sigma0 * ∫ x, vecDot (u.toH1Function.grad x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := by rw [hsymm]
      _ = -(∫ x, vecDot (h x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume) := huNorm v
  have hpair :
      ∫ x, vecDot (G x) (u.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume =
        ∫ x, vecDot (h x) (v.toH1Function.grad x)
          ∂(centeredCubeDomain d m).normalizedVolume := neg_injective hneg
  calc
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (G x) (u.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
          apply integral_congr_ae
          filter_upwards with x
          exact vecDot_comm _ _
    _ = _ := hpair

/-- Cross-pair a supplied centered Neumann solution against the canonical
mean-zero adjoint. -/
theorem centeredCubeMeanZeroScalarDivergenceSolution_normalized_cross_pairing
    {d : ℕ} [NeZero d] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H1MeanZeroFunction (openCubeSet (originCube d m)))
    (h G : Vec d → Vec d)
    (hu : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) sigma0)
      (openCubeSet (originCube d m)) u (fun x ↦ -h x))
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ∫ x, vecDot (u.toH1Function.grad x) (G x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      ∫ x, vecDot (h x)
        ((centeredCubeMeanZeroScalarDivergenceSolution
          m hsigma0 G hG).toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume := by
  exact centeredCubeMeanZeroScalarDivergence_cross_pairing m u
    (centeredCubeMeanZeroScalarDivergenceSolution m hsigma0 G hG) h G hu
    (centeredCubeMeanZeroScalarDivergenceSolution_isWeakSolution
      m hsigma0 G hG)

end CubeCalderonZygmund

end
end Homogenization
