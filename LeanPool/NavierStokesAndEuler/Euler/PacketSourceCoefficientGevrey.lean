/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceCorrectionCoefficients
import LeanPool.NavierStokesAndEuler.Euler.MeanCoefficientPathJets
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderCoefficientBounds
import LeanPool.NavierStokesAndEuler.Euler.PacketMatrixCoefficientGevrey

/-! Source bounds for the actual pressure metric, linear coefficient and
three quadratic coefficients.  Their common coefficient radius and amplitudes
are independent of the correction order, cutoff and frequency. -/

@[expose] public section


noncomputable section

namespace EulerPacketCorrectionCoefficients

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketCylinderField
  EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)
  (R C0 C1 CI : ℝ) (hR : 0 ≤ R) (hC0 : 0 ≤ C0) (hC1 : 0 ≤ C1) (hCI : 0 ≤ CI)
  (hF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C0 * majorant R
      0
      n)
  (hF1 : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C1 * majorant
      R
      0 n)
  (hFI : ∀ n t x, ‖iteratedFDeriv ℝ n (D.FInv.field t : Space → Space →L[ℝ] Space) x‖ ≤ CI *
      majorant
      R 0 n)

include hR hC0 hF in
theorem frameCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (frameCoefficient D).path) a‖ ≤ C0*majorant R 0 n
        :=
  D.F.norm_iteratedFDeriv_translation_le n (C0*majorant R 0 n)
    (mul_nonneg hC0 (majorant_nonneg R hR 0 n)) (hF n) a

include hR hC1 hF1 in
theorem frameTimeCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (frameTimeCoefficient D).path) a‖ ≤ C1*majorant R
        0 n :=
  D.F₁.norm_iteratedFDeriv_translation_le n (C1*majorant R 0 n)
    (mul_nonneg hC1 (majorant_nonneg R hR 0 n)) (hF1 n) a

include hR hCI hFI in
theorem inverseCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (inverseCoefficient D).path) a‖ ≤ CI*majorant R 0
        n :=
  D.FInv.norm_iteratedFDeriv_translation_le n (CI*majorant R 0 n)
    (mul_nonneg hCI (majorant_nonneg R hR 0 n)) (hFI n) a

include hR hCI hFI in
theorem metricCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (metricCoefficient D).path) a‖ ≤
      (3*CI*CI)*majorant (4*R) 0 n := by
  have hi := inverseCoefficient_bound D R CI hR hCI hFI
  exact MatrixCoefficient.bound_mono_radius (metricCoefficient D) R (4*R) (3*CI*CI)
    hR (by linarith) (by positivity)
    (MatrixCoefficient.comp_bound (inverseCoefficient D) (inverseCoefficient D).adjoint
      R CI CI hR hCI hCI hi ((inverseCoefficient D).adjoint_bound R CI hi)) n a

include hR hC1 hCI hF1 hFI in
theorem linearCoefficient_bound (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (linearCoefficient D).path) a‖ ≤
      (6*CI*C1)*majorant (4*R) 0 n := by
  have hi := inverseCoefficient_bound D R CI hR hCI hFI
  have h1 := frameTimeCoefficient_bound D R C1 hR hC1 hF1
  have hp := MatrixCoefficient.comp_bound (inverseCoefficient D) (frameTimeCoefficient D)
    R CI C1 hR hCI hC1 hi h1
  have hs := MatrixCoefficient.smul_bound ((inverseCoefficient D).comp (frameTimeCoefficient D))
    2 R (3*CI*C1) hp
  apply MatrixCoefficient.bound_mono_radius (linearCoefficient D) R (4*R) (6*CI*C1)
    hR (by linarith) (by positivity) _ n a
  intro k x
  simpa only [linearCoefficient,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
    (hs k x).trans_eq (show (|2| * (3*CI*C1))*majorant R 0 k =
      (6*CI*C1)*majorant R 0 k by rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]; ring)

include hR hC0 hCI hF hFI in
theorem quadraticCoefficient_bound (κ : ℝ) (hκ : |κ| ≤ 1) (i : Fin 3) (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (quadraticCoefficient D κ i).path) a‖ ≤
      (3*CI*(C0*R))*majorant (4*R) 0 n := by
  have hi := MatrixCoefficient.bound_mono_radius (inverseCoefficient D) R (4*R) CI
    hR (by linarith) hCI (inverseCoefficient_bound D R CI hR hCI hFI)
  have hunit : ‖(EuclideanSpace.single i 1 : Space)‖ ≤ 1 := by simp
  have hd := MatrixCoefficient.spatialDerivative_bound (frameCoefficient D)
    (EuclideanSpace.single i 1) hunit R C0 hR hC0 (frameCoefficient_bound D R C0 hR hC0 hF)
  have hp := MatrixCoefficient.comp_bound (inverseCoefficient D)
    ((frameCoefficient D).spatialDerivative (EuclideanSpace.single i 1))
    (4*R) CI (C0*R) (by positivity) hCI (by positivity) hi hd
  have hs := MatrixCoefficient.smul_bound
    ((inverseCoefficient D).comp ((frameCoefficient D).spatialDerivative (EuclideanSpace.single i
        1)))
    κ (4*R) (3*CI*(C0*R)) hp n a
  exact hs.trans (by
    have hnon : 0 ≤ (3*CI*(C0*R))*majorant (4*R) 0 n :=
      mul_nonneg (by positivity) (majorant_nonneg (4*R) (by positivity) 0 n)
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hκ hnon)

end EulerPacketCorrectionCoefficients
