/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.FluxComparisonDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.ParentTruncatedHomogenizationError
import LeanPool.CoarseGraining.Homogenization.Besov.Positive.ExactOverlapEuclideanLp

/-!
# Exact local finite-`p` coarse-graining carriers

This file owns the source-facing local finite-`p` coarse-graining definitions
from the ABK26 statement.  It reuses the canonical running-scale negative
Besov seminorm, overlap positive Besov seminorm, and parent-truncated errors.
-/

namespace Homogenization
namespace Book
namespace Ch03
namespace ABK26

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem memLp_hilbertify_normalizedCube_of_memVectorL2 {d : ℕ}
    {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemVectorL2 (openCubeSet Q) F) :
    MemLp (fun x => HilbertVec.ofVec (F x)) 2 (normalizedCubeMeasure Q) := by
  have hHilbert : MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (volumeMeasureOn (openCubeSet Q)) :=
    memHilbertVectorL2_hilbertifyVecField hF
  simpa only [volumeMeasureOn, normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
    hHilbert.smul_measure ENNReal.ofReal_ne_top

private theorem memVectorL2_matVecMul_pointwiseCoeffOn {d : ℕ}
    (Q : TriadicCube d) (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (a.toCoeffField x) (u.grad x)) := by
  let b : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q) :=
    Internal.Ch02.BookCh02.pointwiseCoeffOn (Book.Ch02.cubeDomain Q) a
  have hEll : IsEllipticFieldOn b.lam b.Lam (openCubeSet Q) b.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using
      Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn
        (Book.Ch02.cubeDomain Q) a
  have hB : MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (b.toCoeffField x) (u.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
  have hba : b.toCoeffField =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa only [b, Book.Ch02.cubeDomain_coe] using!
      Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq (Book.Ch02.cubeDomain Q) a
  apply (memLp_congr_ae ?_).mp hB
  filter_upwards [hba] with x hx
  simp only [hx]

private theorem memVectorL2_localFluxDefect {d : ℕ}
    {Q R : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) (sigma0 : ℝ)
    (u : H1Function (openCubeSet Q)) :
    MemVectorL2 (openCubeSet R)
      (fun x => matVecMul
        (a.toCoeffField x - scalarMatrix (d := d) sigma0) (u.grad x)) := by
  let aR : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R) :=
    a.restrictToSubcube hRQ
  let uR : H1Function (openCubeSet R) :=
    u.restrict (isOpen_openCubeSet R) hRQ
  have hflux : MemVectorL2 (openCubeSet R)
      (fun x => matVecMul (aR.toCoeffField x) (uR.grad x)) :=
    memVectorL2_matVecMul_pointwiseCoeffOn R aR uR
  have hscalar : MemVectorL2 (openCubeSet R)
      (fun x => sigma0 • uR.grad x) :=
    uR.grad_memVectorL2.const_smul sigma0
  have hsub := hflux.sub hscalar
  simpa only [aR, uR, Book.Ch02.CoeffOn.restrictToSubcube_toCoeffField,
    H1Function.restrict, sub_matVecMul, matVecMul_scalarMatrix] using! hsub

/-- Full finite-`p` fractional Sobolev membership on a cube. -/
def MemCubeEuclideanFullWsp {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) : Prop :=
  MeasureTheory.MemLp (fun x => HilbertVec.ofVec (g x)) p.exponent
      (normalizedCubeMeasure Q) ∧
    MemCubeEuclideanWsp Q s p g

/-- Weak form of the heterogeneous forced equation on a cube. -/
def IsForcedEquation {d : ℕ} (Q : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function (openCubeSet Q),
    (∫ x in openCubeSet Q,
        vecDot (matVecMul (a.toCoeffField x) (u.grad x))
          (phi.toH1Function.grad x) ∂MeasureTheory.volume) =
      -(∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂MeasureTheory.volume)

/-- Weak form of the scalar-comparator forced equation on a cube. -/
def IsScalarForcedEquation {d : ℕ} (Q : TriadicCube d) (sigma0 : ℝ)
    (v : H1Function (openCubeSet Q)) (g : Vec d → Vec d) : Prop :=
  ∀ phi : H10Function (openCubeSet Q),
    (∫ x in openCubeSet Q,
        vecDot (matVecMul (scalarMatrix (d := d) sigma0) (v.grad x))
          (phi.toH1Function.grad x) ∂MeasureTheory.volume) =
      -(∫ x in openCubeSet Q,
        vecDot (g x) (phi.toH1Function.grad x) ∂MeasureTheory.volume)

/-- Function-level zero-trace difference on an arbitrary cube. -/
def HasH10Difference {d : ℕ} (Q : TriadicCube d)
    (u v : H1Function (openCubeSet Q)) : Prop :=
  ∃ w : H10Function (openCubeSet Q),
    w.toH1Function.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => u.toFun x - v.toFun x

/-- The literal gradient difference, bundled with its `L²` certificate. -/
noncomputable def gradientDifferenceL2Field {d : ℕ}
    (Q : TriadicCube d) (u v : H1Function (openCubeSet Q)) :
    CubeEuclideanLpField Q FiniteLpExponent.two where
  toField := fun x => u.grad x - v.grad x
  euclideanMemLp := by
    rw [memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply, Pi.sub_apply] using!
      (u.grad_memL2_normalizedCubeMeasure i).sub
        (v.grad_memL2_normalizedCubeMeasure i)

/-- The literal heterogeneous/scalar flux difference, bundled with `L²`. -/
noncomputable def fluxDifferenceL2Field {d : ℕ}
    (Q : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q)) (sigma0 : ℝ)
    (u v : H1Function (openCubeSet Q)) :
    CubeEuclideanLpField Q FiniteLpExponent.two where
  toField := fun x =>
    matVecMul (a.toCoeffField x) (u.grad x) -
      matVecMul (scalarMatrix (d := d) sigma0) (v.grad x)
  euclideanMemLp := by
    apply memLp_hilbertify_normalizedCube_of_memVectorL2
    simpa only [matVecMul_scalarMatrix] using!
      (memVectorL2_matVecMul_pointwiseCoeffOn Q a u).sub
        (v.grad_memVectorL2.const_smul sigma0)

/-- The canonical reusable overlap positive Besov seminorm. -/
noncomputable abbrev cubeEuclideanPositiveBesovOverlapESeminorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) : ℝ≥0∞ :=
  Homogenization.cubeEuclideanPositiveBesovOverlapESeminorm Q s p g

/-- Restriction of an `H¹` function to a subcube. -/
noncomputable def restrictH1ToSubcube {d : ℕ} {Q R : TriadicCube d}
    (u : H1Function (openCubeSet Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    H1Function (openCubeSet R) :=
  u.restrict (isOpen_openCubeSet R) hRQ

@[simp] theorem restrictH1ToSubcube_toFun {d : ℕ} {Q R : TriadicCube d}
    (u : H1Function (openCubeSet Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    (restrictH1ToSubcube u hRQ).toFun = u.toFun := rfl

@[simp] theorem restrictH1ToSubcube_grad {d : ℕ} {Q R : TriadicCube d}
    (u : H1Function (openCubeSet Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    (restrictH1ToSubcube u hRQ).grad = u.grad := rfl

/-- The normalized symmetric local energy. -/
noncomputable def localSymmetricEnergyENorm {d : ℕ}
    (R : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain R))
    (u : H1Function (openCubeSet R)) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal
      (vecDot (u.grad x)
        (matVecMul (symmPart (a.toCoeffField x)) (u.grad x)))
      ∂normalizedCubeMeasure R) ^ (1 / 2 : ℝ)

/-- The weighted descendant `ell^p` aggregation of local symmetric energies. -/
noncomputable def weightedLocalSymmetricEnergyLp {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (u : H1Function (openCubeSet Q))
    (s1 s : FractionalOrder) (p : FiniteLpExponent) : ℝ≥0∞ := by
  classical
  exact (∑' j : ℕ,
    ENNReal.ofReal
        (Real.rpow 3 (-((s.1 - s1.1) * p.exponent.toReal * (j : ℝ)))) *
      ((descendantsAtScale Q (n - (j : ℤ))).card : ℝ≥0∞)⁻¹ *
      (descendantsAtScale Q (n - (j : ℤ))).attach.sum (fun R =>
        (localSymmetricEnergyENorm R.1
          (a.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))
          (restrictH1ToSubcube u
            (openCubeSet_subset_of_mem_descendantsAtScale (by omega) R.2))) ^
          p.exponent.toReal)) ^ (1 / p.exponent.toReal)

/-- The local scalar-comparator flux defect on a subcube. -/
noncomputable def localFluxDefectL2Field {d : ℕ}
    {Q R : TriadicCube d}
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) (sigma0 : ℝ)
    (u : H1Function (openCubeSet Q)) :
    CubeEuclideanLpField R FiniteLpExponent.two where
  toField := fun x =>
    matVecMul
      (a.toCoeffField x - scalarMatrix (d := d) sigma0) (u.grad x)
  euclideanMemLp := by
    apply memLp_hilbertify_normalizedCube_of_memVectorL2
    exact memVectorL2_localFluxDefect a hRQ sigma0 u

/-- The normalized `ell^p` average of descendant negative Besov flux defects. -/
noncomputable def localFluxDefectNegativeBesovLpAverage {d : ℕ}
    [NeZero d] (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (u : H1Function (openCubeSet Q))
    (s : FractionalOrder) (p : FiniteLpExponent) : ℝ≥0∞ := by
  classical
  exact ENNReal.ofReal (Real.rpow 3 (-s.1 * (n : ℝ))) *
    (((descendantsAtScale Q n).card : ℝ≥0∞)⁻¹ *
      (descendantsAtScale Q n).attach.sum (fun R =>
        (cubeEuclideanNegativeBesovESeminorm R.1 s p
          (localFluxDefectL2Field a
            (openCubeSet_subset_of_mem_descendantsAtScale hn R.2)
            sigma0 u)) ^ p.exponent.toReal)) ^
      (1 / p.exponent.toReal)

/-- The exact right-hand side of the local finite-`p` coarse-graining bound. -/
noncomputable def localCoarseGrainingLpRHS {d : ℕ} [NeZero d]
    (C : ℝ≥0∞) (Q : TriadicCube d) (n : ℤ) (hn : n ≤ Q.scale)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    (sigma0 : ℝ) (hsigma0 : 0 < sigma0)
    (g : Vec d → Vec d) (u : H1Function (openCubeSet Q))
    (s1 s s2 : FractionalOrder) (p : FiniteLpExponent) : ℝ≥0∞ :=
  C * (ENNReal.ofReal s.1)⁻¹ * (ENNReal.ofReal sigma0) ^ (1 / 2 : ℝ) *
      Book.Ch02.parentTruncatedHomogenizationErrorInfinityOneScalar
        Q n hn a sigma0 hsigma0 s1 *
      weightedLocalSymmetricEnergyLp Q n hn a u s1 s p +
    C * (ENNReal.ofReal s.1) ^ (-(9 / 2 : ℝ)) *
      (ENNReal.ofReal (s2.1 - s.1))⁻¹ *
      (1 +
        (Book.Ch02.parentTruncatedHomogenizationErrorInfinityTwoScalar
          Q n hn a sigma0 hsigma0 (fractionalOrderHalf s1)) ^ 2) *
      ENNReal.ofReal (Real.rpow 3 (s2.1 * (n : ℝ))) *
      cubeEuclideanPositiveBesovOverlapESeminorm Q s2 p g

end

end ABK26
end Ch03
end Book
end Homogenization
