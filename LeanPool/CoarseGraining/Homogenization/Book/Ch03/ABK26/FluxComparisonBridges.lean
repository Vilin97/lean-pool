/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.FluxComparisonDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.PublicInternalBridges.H1Transport
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp

/-!
# Structural bridges for the Chapter 3 flux-comparison estimate

This module converts the exact public hypotheses of the source-facing
flux-comparison statement into the representative-level potential and
solenoidal predicates used by the deterministic testing layer.  It contains
only algebraic and measure-normalization bridges; no quantitative estimate is
proved here.
-/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A zero-trace value difference has the expected gradient difference, up to
the a.e. equality intrinsic to Sobolev functions. -/
theorem HasCenteredCubeH10Difference.exists_grad_ae_eq
    {d : ℕ} {m : ℤ}
    {u v : H1Function (openCubeSet (originCube d m))}
    (hzero : HasCenteredCubeH10Difference m u v) :
    ∃ w : H10Function (openCubeSet (originCube d m)),
      w.toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        fun x => u.grad x - v.grad x := by
  rcases hzero with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  have hw' :
      w.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        (u - v).toFun := by
    simpa only [H1Function.sub_toFun] using hw
  have hgrad := H1Function.grad_ae_eq_of_toFun_ae_eq
    (isOpen_openCubeSet (originCube d m))
    (u := w.toH1Function) (v := u - v) hw'
  simpa only [H1Function.sub_grad] using hgrad

/-- The source-facing zero-trace difference hypothesis supplies the exact
potential predicate for the gradient difference on the open cube. -/
theorem HasCenteredCubeH10Difference.isPotentialZeroTraceOn_openCubeSet
    {d : ℕ} {m : ℤ}
    {u v : H1Function (openCubeSet (originCube d m))}
    (hzero : HasCenteredCubeH10Difference m u v) :
    IsPotentialZeroTraceOn (openCubeSet (originCube d m))
      (fun x => u.grad x - v.grad x) := by
  rcases hzero.exists_grad_ae_eq with ⟨w, hw⟩
  exact IsPotentialZeroTraceOn.congr_ae hw w.isPotentialZeroTraceOn

/-- The same zero-trace potential, transported to the half-open cube used by
the deterministic testing API. -/
theorem HasCenteredCubeH10Difference.isPotentialZeroTraceOn_cubeSet
    {d : ℕ} [NeZero d] {m : ℤ}
    {u v : H1Function (openCubeSet (originCube d m))}
    (hzero : HasCenteredCubeH10Difference m u v) :
    IsPotentialZeroTraceOn (cubeSet (originCube d m))
      (fun x => u.grad x - v.grad x) := by
  exact isPotentialZeroTraceOn_cubeSet_triadicCube_of_openCubeSet
    hzero.isPotentialZeroTraceOn_openCubeSet

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem centeredCube_normalization_factor_ne_zero {d : ℕ} (m : ℤ) :
    (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal ≠ 0 := by
  rw [ENNReal.toReal_ofReal (inv_nonneg.2 (cubeVolume_nonneg _))]
  exact (inv_ne_zero (cubeVolume_pos _).ne')

/-- A raw cube Dirichlet divergence problem is the same weak equation after
moving to the normalized centered-cube measure. -/
theorem cubeDirichletDivergenceProblem_to_centeredCubeH10ScalarDivergenceSolution
    {d : ℕ} {p : FiniteLpExponent} (m : ℤ)
    {z : H10Function (openCubeSet (originCube d m))}
    {h : CubeEuclideanLpField (originCube d m) p}
    (hh : MemLp (fun x => HilbertVec.ofVec (h.toField x)) 2
      (normalizedCubeMeasure (originCube d m)))
    (hz : CubeDirichletDivergenceProblem (originCube d m) z h.toField) :
    IsCenteredCubeH10ScalarDivergenceSolution m 1 z ⟨h.toField, hh⟩ := by
  intro phi
  have hmeasure := centeredCube_normalizedVolume_eq_smul_openCubeVolume (d := d) m
  rw [hmeasure, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure, smul_eq_mul, smul_eq_mul, one_mul,
    hz phi]
  ring

/-- The same normalization bridge when the datum already carries both its
finite-exponent and `L²` certificates. -/
theorem CubeEuclideanL2LpField.to_centeredCubeH10ScalarDivergenceSolution
    {d : ℕ} {p : FiniteLpExponent} (m : ℤ)
    (h : CubeEuclideanL2LpField (originCube d m) p)
    (z : H10Function (openCubeSet (originCube d m)))
    (hz : CubeDirichletDivergenceProblem (originCube d m) z h.toField) :
    IsCenteredCubeH10ScalarDivergenceSolution m 1 z h.toLpTwo := by
  simpa only [CubeEuclideanL2LpField.toLpTwo] using
    cubeDirichletDivergenceProblem_to_centeredCubeH10ScalarDivergenceSolution
      m h.euclideanMemL2 hz

/-- The normalized weak flux balance is equivalent to raw solenoidality on
the open cube: the positive volume-normalization factor cancels. -/
theorem IsCenteredCubeFluxBalanced.isSolenoidalOn_openCubeSet
    {d : ℕ} {m : ℤ}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))}
    {sigma0 : ℝ} {u v : H1Function (openCubeSet (originCube d m))}
    (hbal : IsCenteredCubeFluxBalanced m a sigma0 u v) :
    IsSolenoidalOn (openCubeSet (originCube d m))
      (fun x => matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x) := by
  intro phi
  have hphi := hbal phi
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume] at hphi
  rw [MeasureTheory.integral_smul_measure] at hphi
  rw [smul_eq_mul] at hphi
  exact (mul_eq_zero.mp hphi).resolve_left
    (centeredCube_normalization_factor_ne_zero m)

/-- The raw solenoidal field, transported to the half-open cube used by the
deterministic testing API. -/
theorem IsCenteredCubeFluxBalanced.isSolenoidalOn_cubeSet
    {d : ℕ} [NeZero d] {m : ℤ}
    {a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m))}
    {sigma0 : ℝ} {u v : H1Function (openCubeSet (originCube d m))}
    (hbal : IsCenteredCubeFluxBalanced m a sigma0 u v) :
    IsSolenoidalOn (cubeSet (originCube d m))
      (fun x => matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x) := by
  exact isSolenoidalOn_cubeSet_triadicCube_of_openCubeSet
    hbal.isSolenoidalOn_openCubeSet

/-- The root scalar-comparator flux defect, with the literal representative
used in every descendant defect. -/
noncomputable def centeredCubeRootFluxDefectL2Field {d : ℕ}
    (m : ℤ)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
    (sigma0 : ℝ) (u : H1Function (openCubeSet (originCube d m))) :
    CubeEuclideanLpField (originCube d m) FiniteLpExponent.two where
  toField := fun x =>
    matVecMul (a.toCoeffField x - scalarMatrix (d := d) sigma0) (u.grad x)
  euclideanMemLp := by
    have h := (centeredCubeFluxDifferenceL2Field m a sigma0 u u).euclideanMemLp
    simpa only [centeredCubeFluxDifferenceL2Field, sub_matVecMul,
      matVecMul_scalarMatrix] using h

/-- Exact pointwise decomposition of the global flux into the scalar gradient
difference and the root coefficient defect. -/
theorem centeredCubeFluxDifference_eq_smul_gradientDifference_add_rootDefect
    {d : ℕ} (m : ℤ)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
    (sigma0 : ℝ) (u v : H1Function (openCubeSet (originCube d m))) :
    (centeredCubeFluxDifferenceL2Field m a sigma0 u v).toField =
      sigma0 • (centeredCubeGradientDifferenceL2Field m u v).toField +
        (centeredCubeRootFluxDefectL2Field m a sigma0 u).toField := by
  funext x
  simp only [centeredCubeFluxDifferenceL2Field,
    centeredCubeGradientDifferenceL2Field, centeredCubeRootFluxDefectL2Field,
    Pi.add_apply, Pi.smul_apply, sub_matVecMul, matVecMul_scalarMatrix]
  module

/-- Every local defect is literally the same representative as the root
defect, merely supplied with the local `L²` certificate. -/
theorem centeredCubeRootFluxDefectL2Field_toField_eq_local
    {d : ℕ} (m n : ℤ) (hnm : n < m)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain (originCube d m)))
    (sigma0 : ℝ) (u : H1Function (openCubeSet (originCube d m)))
    (R : TriadicCube d)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    (centeredCubeRootFluxDefectL2Field m a sigma0 u).toField =
      (centeredCubeLocalFluxDefectL2Field m n hnm a sigma0 u R hR).toField :=
  rfl

end

end ABK26
end Ch03
end Book
end Homogenization
