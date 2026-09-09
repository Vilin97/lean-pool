/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LeanPool.NavierStokesAndEuler.Euler.MeanWeakCurl
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Pressure cancellation against compactly supported solenoidal vector tests.

The scalar pressure needs only ordinary smoothness. In particular, neither
the pressure nor its gradient is assumed to be globally square integrable.
-/

@[expose] public section


noncomputable section

namespace EulerComparatorPressure

open MeasureTheory InnerProductSpace EulerSmoothLimit EulerVectorCalculus
  EulerMeanSolenoidal EulerMeanPressure
open scoped ContDiff

/-- Integration by parts with compact support on the vector test, rather than
on the scalar potential. -/
theorem compact_vector_gradient_integration_by_parts (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) :
    (∫ x, ⟪φ x, gradient p x⟫_ℝ) = -∫ x, p x * divergence φ x := by
  let φi (i : Fin 3) (x : Space) := φ x i
  have hφi (i : Fin 3) : ContDiff ℝ ∞ (φi i) :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hφ
  have hci (i : Fin 3) : HasCompactSupport (φi i) :=
    hc.comp_left (g := fun v : Space => v i) rfl
  have hi₁ (i : Fin 3) : Integrable (fun x => partialDerivative p i x * φi i x) :=
    ((contDiff_partialDerivative p hp i).continuous.mul
      (hφi i).continuous).integrable_of_hasCompactSupport (hci i).mul_left
  have hi₂ (i : Fin 3) : Integrable (fun x => p x * partialDerivative (φi i) i x) :=
    (hp.continuous.mul (contDiff_partialDerivative _ (hφi i)
        i).continuous).integrable_of_hasCompactSupport
        ((hci i).fderiv_apply ℝ (EuclideanSpace.single i 1)).mul_left
  have hibp (i : Fin 3) : (∫ x, partialDerivative p i x * φi i x) =
      -∫ x, p x * partialDerivative (φi i) i x :=
    scalar_test_ibp p (φi i) hp (hφi i) (hci i) i
  have hinner (x : Space) : ⟪φ x, gradient p x⟫_ℝ =
      ∑ i : Fin 3, partialDerivative p i x * φi i x := by
    rw [real_inner_comm, inner_gradient_left]
    have hre : ∑ i : Fin 3, φ x i • (EuclideanSpace.single i 1 : Space) = φ x := by
      simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (φ x)
    calc
      fderiv ℝ p x (φ x) =
          fderiv ℝ p x (∑ i : Fin 3, φ x i • EuclideanSpace.single i 1) :=
        congrArg (fderiv ℝ p x) hre.symm
      _ = ∑ i : Fin 3, partialDerivative p i x * φi i x := by
        simp only [map_sum, map_smul, smul_eq_mul, partialDerivative, φi, mul_comm]
  have hdiv (x : Space) : p x * divergence φ x =
      ∑ i : Fin 3, p x * partialDerivative (φi i) i x := by
    rw [divergence_eq_coordinate_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (fderiv_coordinate φ x ((hφ.differentiable (by simp)).differentiableAt)
      i (EuclideanSpace.single i 1)).symm
  simp_rw [hinner, hdiv]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),
    integral_finsetSum _ (fun i _ => hi₂ i)]
  simp only [hibp, Finset.sum_neg_distrib]

/-- An arbitrary smooth scalar pressure cancels against a compact smooth
divergence-free vector test. -/
theorem compact_solenoidal_pressure_pairing_zero (φ : Space → Space)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hdiv : ∀ x, divergence φ x = 0)
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) :
    (∫ x, ⟪φ x, gradient p x⟫_ℝ) = 0 := by
  rw [compact_vector_gradient_integration_by_parts φ hφ hc p hp]
  simp only [hdiv, mul_zero, integral_zero, neg_zero]

end EulerComparatorPressure
