/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.ABK26.NegativeBesov
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.CoeffRestriction
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
public import LeanPool.CoarseGraining.Homogenization.Ambient.ScalarMatrix
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeEuclideanL2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual

/-!
# Exact carriers for the Chapter 3 flux-comparison estimate

This module owns the literal fields and quantities in the frozen
Armstrong--Kuusi--Loher flux-defect duality statement.  In particular, the
coefficient argument remains the public a.e. `CoeffOn` object; pointwise
representatives are used only privately to establish the `L²` certificates.
-/

@[expose] public section

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

/-- Function-level zero-trace difference on the centered cube. -/
def HasCenteredCubeH10Difference {d : ℕ} (m : ℤ)
    (u v : H1Function (openCubeSet (originCube d m))) : Prop :=
  ∃ w : H10Function (openCubeSet (originCube d m)),
    w.toH1Function.toFun =ᵐ[
      volumeMeasureOn (openCubeSet (originCube d m))]
      fun x => u.toFun x - v.toFun x

/-- The flux difference is weakly divergence-free against zero-trace tests. -/
def IsCenteredCubeFluxBalanced {d : ℕ} (m : ℤ)
    (a : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u v : H1Function (openCubeSet (originCube d m))) : Prop :=
  ∀ phi : H10Function (openCubeSet (originCube d m)),
    ∫ x,
      vecDot
        (matVecMul (a.toCoeffField x) (u.grad x) -
          sigma0 • v.grad x)
        (phi.toH1Function.grad x)
      ∂(centeredCubeDomain d m).normalizedVolume = 0

/-- The centered-cube gradient difference, bundled with its genuine `L²`
certificate. -/
noncomputable def centeredCubeGradientDifferenceL2Field {d : ℕ}
    (m : ℤ) (u v : H1Function (openCubeSet (originCube d m))) :
    CubeEuclideanLpField (originCube d m) FiniteLpExponent.two where
  toField := fun x => u.grad x - v.grad x
  euclideanMemLp := by
    rw [memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply, Pi.sub_apply] using!
      (u.grad_memL2_normalizedCubeMeasure i).sub
        (v.grad_memL2_normalizedCubeMeasure i)

/-- The centered-cube coefficient/scalar flux difference, bundled with its
genuine `L²` certificate. -/
noncomputable def centeredCubeFluxDifferenceL2Field {d : ℕ}
    (m : ℤ)
    (a : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u v : H1Function (openCubeSet (originCube d m))) :
    CubeEuclideanLpField (originCube d m) FiniteLpExponent.two where
  toField := fun x =>
    matVecMul (a.toCoeffField x) (u.grad x) - sigma0 • v.grad x
  euclideanMemLp := by
    apply memLp_hilbertify_normalizedCube_of_memVectorL2
    exact (memVectorL2_matVecMul_pointwiseCoeffOn (originCube d m) a u).sub
      (v.grad_memVectorL2.const_smul sigma0)

/-- The local scalar-comparator flux defect on a descendant. -/
noncomputable def centeredCubeLocalFluxDefectL2Field {d : ℕ}
    (m n : ℤ) (hnm : n < m)
    (a : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u : H1Function (openCubeSet (originCube d m)))
    (R : TriadicCube d)
    (hR : R ∈ descendantsAtScale (originCube d m) n) :
    CubeEuclideanLpField R FiniteLpExponent.two where
  toField := fun x =>
    matVecMul
      (a.toCoeffField x - scalarMatrix (d := d) sigma0) (u.grad x)
  euclideanMemLp := by
    apply memLp_hilbertify_normalizedCube_of_memVectorL2
    exact memVectorL2_localFluxDefect a
      (openCubeSet_subset_of_mem_descendantsAtScale (le_of_lt hnm) hR) sigma0 u

/-- The normalized descendant `ell^p` average of local smooth-dual flux
defects. -/
noncomputable def centeredCubeLocalFluxDefectSmoothDualLpAverage {d : ℕ}
    (m n : ℤ) (hnm : n < m)
    (a : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u : H1Function (openCubeSet (originCube d m)))
    (s : FractionalOrder) (p : FiniteLpExponent) : ℝ≥0∞ := by
  classical
  exact
    (((descendantsAtScale (originCube d m) n).card : ℝ≥0∞)⁻¹ *
      (descendantsAtScale (originCube d m) n).attach.sum (fun R =>
        (cubeEuclideanNegativeWspSmoothDualENorm R.1 s p
          (centeredCubeLocalFluxDefectL2Field
            m n hnm a sigma0 u R.1 R.2)) ^ p.exponent.toReal)) ^
      (p.exponent.toReal)⁻¹

/-- The exact left hand side of the centered-cube flux-comparison estimate. -/
noncomputable def centeredCubeFluxComparisonSmoothDualLHS {d : ℕ}
    (m : ℤ)
    (a : Book.Ch02.CoeffOn
      (Book.Ch02.cubeDomain (originCube d m))) (sigma0 : ℝ)
    (u v : H1Function (openCubeSet (originCube d m)))
    (s : FractionalOrder) (p : FiniteLpExponent) : ℝ≥0∞ :=
  ENNReal.ofReal sigma0 *
      cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
        (centeredCubeGradientDifferenceL2Field m u v) +
    cubeEuclideanNegativeWspSmoothDualENorm (originCube d m) s p
      (centeredCubeFluxDifferenceL2Field m a sigma0 u v)

end

end ABK26
end Ch03
end Book
end Homogenization
