/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.FluxComparisonLocalization
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeFractionalCZFullNorm
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDualFieldPairing

/-!
# Fractional Calderón--Zygmund flux comparison on centered cubes

This is the source-facing assembly of the Chapter 3 deterministic duality
argument.  The public theorem below is deliberately kept to the exact
manuscript hypotheses: the Dirichlet adjoint solve, fractional
Calderón--Zygmund estimate, smooth-dual passage, and descendant localization
are all internal proof steps.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem memLp_vec_of_memLp_hilbert_two {d : ℕ} {Q : TriadicCube d}
    {F : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (normalizedCubeMeasure Q)) :
    MemLp F 2 (normalizedCubeMeasure Q) := by
  apply MemLp.of_eval
  intro i
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i

private theorem memVectorL2_cubeSet_of_cubeEuclideanLpField_two
    {d : ℕ} {Q : TriadicCube d} (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    MemVectorL2 (cubeSet Q) F.toField := by
  apply memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q
  simpa only [FiniteLpExponent.two_exponent] using
    memLp_vec_of_memLp_hilbert_two F.euclideanMemLp

private noncomputable def smoothTestToCubeEuclideanWspL2Field
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) : CubeEuclideanWspL2Field Q s p where
  toField := h.toField
  euclideanMemLp := h.toCubeEuclideanWspField.euclideanMemLp
  euclideanMemWsp := h.toCubeEuclideanWspField.euclideanMemWsp
  euclideanMemL2 := h.euclideanMemLp_two

private noncomputable def smoothTestToCubeEuclideanL2LpField
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) : CubeEuclideanL2LpField Q p where
  toField := h.toField
  euclideanMemLp := h.toCubeEuclideanWspField.euclideanMemLp
  euclideanMemL2 := h.euclideanMemLp_two

private theorem smoothTestToCubeEuclideanWspL2Field_toField
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    (smoothTestToCubeEuclideanWspL2Field h).toField = h.toField := rfl

private theorem exists_centeredCubeDirichlet_adjoint
    {d : ℕ} [NeZero d] (m : ℤ) {s : FractionalOrder}
    {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest (originCube d m) s p) :
    ∃ z : H10Function (openCubeSet (originCube d m)),
      CubeDirichletDivergenceProblem (originCube d m) z h.toField := by
  apply exists_cubeDirichletDivergenceProblem_of_memLp_normalizedCubeMeasure
  exact memLp_vec_of_memLp_hilbert_two h.euclideanMemLp_two

/-- The unit-coefficient adjoint solve for a smooth fractional test, bundled
with both the literal fractional field and its `L²` representative.  The
constant is fixed before the cube, order, and test. -/
private theorem exists_centeredCube_adjGradient_full_cz
    (d : ℕ) [NeZero d] (p : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (s : FractionalOrder)
        (h : CubeEuclideanWspSmoothTest (originCube d m) s p),
        ∃ (z : H10Function (openCubeSet (originCube d m)))
          (gradZ : CubeEuclideanWspL2Field (originCube d m) s p),
          CubeDirichletDivergenceProblem (originCube d m) z h.toField ∧
          gradZ.toField = z.toH1Function.grad ∧
          cubeEuclideanWspFullENorm (originCube d m) s p gradZ.toField ≤
            C * cubeEuclideanWspFullENorm (originCube d m) s p h.toField := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_fractional_cz_full d p
  obtain ⟨Csemi, hCsemi_top, hCsemi⟩ :=
    centeredCubeH10ScalarDivergence_fractional_cz d p
  refine ⟨C, hCtop, ?_⟩
  intro m s h
  rcases exists_centeredCubeDirichlet_adjoint m h with ⟨z, hz⟩
  let hWsp : CubeEuclideanWspL2Field (originCube d m) s p :=
    smoothTestToCubeEuclideanWspL2Field h
  let hLp : CubeEuclideanL2LpField (originCube d m) p :=
    smoothTestToCubeEuclideanL2LpField h
  have hsolution : IsCenteredCubeH10ScalarDivergenceSolution m 1 z hLp.toLpTwo :=
    CubeEuclideanL2LpField.to_centeredCubeH10ScalarDivergenceSolution m hLp z (by
      simpa only [hLp] using! hz)
  have hfull := hC m 1 s hWsp z zero_lt_one (by
    simpa only [hWsp, hLp] using! hsolution)
  obtain ⟨gradW, hgradW, _⟩ := hCsemi m 1 s hWsp z zero_lt_one (by
    simpa only [hWsp, hLp] using! hsolution)
  let gradZ : CubeEuclideanWspL2Field (originCube d m) s p :=
    { toField := gradW.toField
      euclideanMemLp := gradW.euclideanMemLp
      euclideanMemWsp := gradW.euclideanMemWsp
      euclideanMemL2 := by
        rw [memLp_piLp_iff]
        intro i
        simpa only [hgradW, HilbertVec.ofVec, PiLp.toLp_apply] using
          z.toH1Function.grad_memL2_normalizedCubeMeasure i }
  refine ⟨z, gradZ, hz, ?_, ?_⟩
  · simpa only [gradZ] using hgradW
  · dsimp only [gradZ]
    rw [hgradW]
    simpa only [ENNReal.ofReal_one, inv_one, one_mul, mul_one, hWsp,
      smoothTestToCubeEuclideanWspL2Field_toField] using hfull

/-- The normalized adjoint-testing identity, specialized to the literal
centered-cube flux decomposition.  This is deliberately a real-valued
identity; the subsequent smooth-dual estimate applies `ofReal ∘ |·|`. -/
private theorem centeredCube_adjoint_testing_identity
    {d : ℕ} [NeZero d] {m : ℤ}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))}
    {sigma0 : ℝ} {u v : H1Function (openCubeSet (originCube d m))}
    {h : Vec d → Vec d} {z : H10Function (openCubeSet (originCube d m))}
    (hbal : IsCenteredCubeFluxBalanced m a sigma0 u v)
    (hzero : HasCenteredCubeH10Difference m u v)
    (hz : CubeDirichletDivergenceProblem (originCube d m) z h) :
    sigma0 * cubeAverage (originCube d m)
        (fun x => vecDot
          ((centeredCubeGradientDifferenceL2Field m u v).toField x) (h x)) =
      cubeAverage (originCube d m)
        (fun x => vecDot
          ((centeredCubeRootFluxDefectL2Field m a sigma0 u).toField x)
          (z.toH1Function.grad x)) := by
  let Q : TriadicCube d := originCube d m
  let w := (centeredCubeGradientDifferenceL2Field m u v).toField
  let F := (centeredCubeRootFluxDefectL2Field m a sigma0 u).toField
  have hw : IsPotentialZeroTraceOn (cubeSet Q) w := by
    simpa only [Q, w] using! hzero.isPotentialZeroTraceOn_cubeSet
  have hF : MemVectorL2 (cubeSet Q) F := by
    simpa only [Q, F] using
      memVectorL2_cubeSet_of_cubeEuclideanLpField_two
        (centeredCubeRootFluxDefectL2Field m a sigma0 u)
  have hsol : IsSolenoidalOn (cubeSet Q)
      (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) := by
    rw [show (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) =
        (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField by
      calc
        (fun x => matVecMul (scalarMatrix (d := d) sigma0) (w x) + F x) =
            sigma0 • (centeredCubeGradientDifferenceL2Field m u v).toField +
              (centeredCubeRootFluxDefectL2Field m a sigma0 u).toField := by
              funext x
              simp only [w, F, matVecMul_scalarMatrix]
              rfl
        _ = (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField :=
          (centeredCubeFluxDifference_eq_smul_gradientDifference_add_rootDefect
            m a sigma0 u v).symm]
    simpa only [Q] using! hbal.isSolenoidalOn_cubeSet
  have hraw := dirichletDivergence_solutionComparison_integral_identity
    (Q := Q) (sigma0 := sigma0) (w := w) (F := F) (h := h) (v := z)
      hF (by simpa only [Q] using hz) hw hsol
  rw [cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet,
    cubeAverage_eq_inv_cubeVolume_mul_setIntegral_openCubeSet]
  have hraw' : sigma0 *
      ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume =
      ∫ x in openCubeSet Q, vecDot (F x) (z.toH1Function.grad x)
        ∂MeasureTheory.volume := by
    simpa only [matVecMul_scalarMatrix, vecDot_smul_left,
      MeasureTheory.integral_const_mul] using hraw
  calc
    sigma0 * ((cubeVolume Q)⁻¹ *
        ∫ x in openCubeSet Q, vecDot (w x) (h x) ∂MeasureTheory.volume) =
        (cubeVolume Q)⁻¹ *
          (sigma0 * ∫ x in openCubeSet Q, vecDot (w x) (h x)
            ∂MeasureTheory.volume) := by ring
    _ = (cubeVolume Q)⁻¹ *
          ∫ x in openCubeSet Q, vecDot (F x) (z.toH1Function.grad x)
            ∂MeasureTheory.volume := by rw [hraw']

/-- Smooth-dual subadditivity in the exact form needed for the literal flux
decomposition. -/
private theorem cubeEuclideanNegativeWspSmoothDualENorm_le_smul_add
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F G H : CubeEuclideanLpField Q FiniteLpExponent.two) (c : ℝ)
    (hc : 0 ≤ c) (hFG : G.toField = c • F.toField + H.toField) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p G ≤
      ENNReal.ofReal c * cubeEuclideanNegativeWspSmoothDualENorm Q s p F +
        cubeEuclideanNegativeWspSmoothDualENorm Q s p H := by
  unfold cubeEuclideanNegativeWspSmoothDualENorm
  apply iSup_le
  rintro ⟨h, hh⟩
  have hpair : cubeEuclideanNormalizedSmoothPairing G h =
      c * cubeEuclideanNormalizedSmoothPairing F h +
        cubeEuclideanNormalizedSmoothPairing H h := by
    unfold cubeEuclideanNormalizedSmoothPairing
    rw [hFG]
    calc
      ∫ x, vecDot ((c • F.toField + H.toField) x) (h.toField x)
          ∂normalizedCubeMeasure Q =
          ∫ x, (c * vecDot (F.toField x) (h.toField x) +
            vecDot (H.toField x) (h.toField x)) ∂normalizedCubeMeasure Q := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              simp only [Pi.add_apply, Pi.smul_apply, vecDot_add_left, vecDot_smul_left]
      _ = c * ∫ x, vecDot (F.toField x) (h.toField x)
            ∂normalizedCubeMeasure Q +
          ∫ x, vecDot (H.toField x) (h.toField x)
            ∂normalizedCubeMeasure Q := by
              rw [MeasureTheory.integral_add
                ((cubeEuclideanNormalizedSmoothPairing_integrable F h).const_mul c)
                (cubeEuclideanNormalizedSmoothPairing_integrable H h),
                MeasureTheory.integral_const_mul]
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing G h| =
        ENNReal.ofReal |c * cubeEuclideanNormalizedSmoothPairing F h +
          cubeEuclideanNormalizedSmoothPairing H h| := by rw [hpair]
    _ ≤ ENNReal.ofReal (|c * cubeEuclideanNormalizedSmoothPairing F h| +
          |cubeEuclideanNormalizedSmoothPairing H h|) :=
      ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |c * cubeEuclideanNormalizedSmoothPairing F h| +
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H h| := by
      rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    _ = ENNReal.ofReal c *
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| +
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H h| := by
          rw [abs_mul, abs_of_nonneg hc, ENNReal.ofReal_mul hc]
    _ ≤ ENNReal.ofReal c *
          cubeEuclideanNegativeWspSmoothDualENorm Q s p F +
        cubeEuclideanNegativeWspSmoothDualENorm Q s p H := by
          gcongr
          · exact le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
              ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F u.1|) ⟨h, hh⟩
          · exact le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
              ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing H u.1|) ⟨h, hh⟩

/-- The adjoint solve turns the smooth-dual gradient difference into the
smooth-dual root flux defect, with a cube-uniform CZ constant. -/
private theorem exists_centeredCube_gradient_negativeDual_le_rootDefect
    (d : ℕ) [NeZero d] (p : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (sigma0 : ℝ), 0 < sigma0 →
        ∀ (s : FractionalOrder)
          (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
          (u v : H1Function (openCubeSet (originCube d m))),
          IsCenteredCubeFluxBalanced m a sigma0 u v →
          HasCenteredCubeH10Difference m u v →
          ENNReal.ofReal sigma0 *
              cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
                (centeredCubeGradientDifferenceL2Field m u v) ≤
            C * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
              (centeredCubeRootFluxDefectL2Field m a sigma0 u) := by
  obtain ⟨C, hCtop, hC⟩ := exists_centeredCube_adjGradient_full_cz d p.conjugate
  refine ⟨C, hCtop, ?_⟩
  intro m sigma0 hsigma0 s a u v hbal hzero
  change ENNReal.ofReal sigma0 * (⨆ h :
      CubeEuclideanWspSmoothUnitTest (originCube d m) s p.conjugate,
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing
        (centeredCubeGradientDifferenceL2Field m u v) h.1|) ≤ _
  rw [ENNReal.mul_iSup]
  apply iSup_le
  rintro ⟨h, hh⟩
  obtain ⟨z, gradZ, hz, hgradZ, hfull⟩ := hC m s h
  have htest := centeredCube_adjoint_testing_identity hbal hzero
    (h := h.toField) hz
  have htest' : sigma0 *
      cubeEuclideanNormalizedSmoothPairing
        (centeredCubeGradientDifferenceL2Field m u v) h =
      cubeEuclideanNormalizedFieldPairing
        (centeredCubeRootFluxDefectL2Field m a sigma0 u) gradZ := by
    unfold cubeEuclideanNormalizedSmoothPairing cubeEuclideanNormalizedFieldPairing
    rw [hgradZ]
    simpa only [cubeAverage_eq_integral_normalizedCubeMeasure] using htest
  have hscale : ENNReal.ofReal sigma0 * ENNReal.ofReal
      |cubeEuclideanNormalizedSmoothPairing
        (centeredCubeGradientDifferenceL2Field m u v) h| =
      ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing
        (centeredCubeRootFluxDefectL2Field m a sigma0 u) gradZ| := by
    calc
      ENNReal.ofReal sigma0 * ENNReal.ofReal
          |cubeEuclideanNormalizedSmoothPairing
            (centeredCubeGradientDifferenceL2Field m u v) h| =
          ENNReal.ofReal (sigma0 * |cubeEuclideanNormalizedSmoothPairing
            (centeredCubeGradientDifferenceL2Field m u v) h|) :=
        (ENNReal.ofReal_mul hsigma0.le).symm
      _ = ENNReal.ofReal |sigma0 * cubeEuclideanNormalizedSmoothPairing
          (centeredCubeGradientDifferenceL2Field m u v) h| := by
            rw [abs_mul, abs_of_pos hsigma0]
      _ = ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) gradZ| := by
            rw [htest']
  have hpair := ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le
    (centeredCubeRootFluxDefectL2Field m a sigma0 u) gradZ
  calc
    ENNReal.ofReal sigma0 * ENNReal.ofReal
        |cubeEuclideanNormalizedSmoothPairing
          (centeredCubeGradientDifferenceL2Field m u v) h| =
        ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) gradZ| := hscale
    _ ≤ cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) *
        cubeEuclideanWspFullENorm (originCube d m) s p.conjugate gradZ.toField := hpair
    _ ≤ cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) *
        (C * cubeEuclideanWspFullENorm (originCube d m) s p.conjugate h.toField) := by
          gcongr
    _ ≤ cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) * C := by
          gcongr
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hh (zero_le : (0 : ℝ≥0∞) ≤ C)
    _ = C * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) := by ac_rfl
theorem exists_centeredCubeFluxComparison_cz
    (d : ℕ) (hd : 2 ≤ d) (p : FiniteLpExponent)
    (hp : (2 : ℝ≥0∞) ≤ p.exponent) :
    letI : NeZero d := ⟨by omega⟩
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m n : ℤ) (hnm : n < m)
        (a : Book.Ch02.CoeffOn
          (Book.Ch02.cubeDomain (originCube d m)))
        (sigma0 : ℝ), 0 < sigma0 →
      ∀ (s : FractionalOrder)
        (u v : H1Function (openCubeSet (originCube d m))),
        IsCenteredCubeFluxBalanced m a sigma0 u v →
        HasCenteredCubeH10Difference m u v →
          centeredCubeFluxComparisonSmoothDualLHS
              m a sigma0 u v s p ≤
            C * ENNReal.ofReal
                (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ)))) *
              centeredCubeLocalFluxDefectSmoothDualLpAverage
                m n hnm a sigma0 u s p := by
  let : NeZero d := ⟨by omega⟩
  obtain ⟨Ccz, hCcz_top, hCcz⟩ :=
    exists_centeredCube_gradient_negativeDual_le_rootDefect d p
  refine ⟨2 * Ccz + 1, ?_, ?_⟩
  · exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by simp) hCcz_top, ENNReal.one_lt_top⟩
  intro m n hnm a sigma0 hsigma0 s u v hbal hzero
  have hgradient := hCcz m sigma0 hsigma0 s a u v hbal hzero
  have hflux := cubeEuclideanNegativeWspSmoothDualENorm_le_smul_add
    (s := s) (p := p)
    (centeredCubeGradientDifferenceL2Field m u v)
    (centeredCubeFluxDifferenceL2Field m a sigma0 u v)
    (centeredCubeRootFluxDefectL2Field m a sigma0 u) sigma0 hsigma0.le
    (centeredCubeFluxDifference_eq_smul_gradientDifference_add_rootDefect
      m a sigma0 u v)
  have hflux' :
      cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeFluxDifferenceL2Field m a sigma0 u v) ≤
        Ccz * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) +
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u) :=
    hflux.trans (by
      simpa only [add_comm] using add_le_add_left hgradient
        (cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeRootFluxDefectL2Field m a sigma0 u)))
  have hlocal := centeredCubeRootFluxDefectL2Field_negativeWspSmoothDual_localize
    m n hnm a sigma0 u s p
  unfold centeredCubeFluxComparisonSmoothDualLHS
  calc
    ENNReal.ofReal sigma0 *
          cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
            (centeredCubeGradientDifferenceL2Field m u v) +
        cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
          (centeredCubeFluxDifferenceL2Field m a sigma0 u v) ≤
        Ccz * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
            (centeredCubeRootFluxDefectL2Field m a sigma0 u) +
          (Ccz * cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
            (centeredCubeRootFluxDefectL2Field m a sigma0 u) +
            cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
              (centeredCubeRootFluxDefectL2Field m a sigma0 u)) := by
          exact add_le_add hgradient hflux'
    _ = (2 * Ccz + 1) *
          cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
            (centeredCubeRootFluxDefectL2Field m a sigma0 u) := by ring
    _ ≤ (2 * Ccz + 1) *
          (ENNReal.ofReal (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ)))) *
            centeredCubeLocalFluxDefectSmoothDualLpAverage
              m n hnm a sigma0 u s p) := by
          exact mul_le_mul_of_nonneg_left hlocal (zero_le)
    _ = (2 * Ccz + 1) * ENNReal.ofReal
          (Real.rpow 3 (s.1 * (((m - n : ℤ) : ℝ)))) *
        centeredCubeLocalFluxDefectSmoothDualLpAverage
          m n hnm a sigma0 u s p := by ac_rfl

end

end ABK26
end Ch03
end Book
end Homogenization
