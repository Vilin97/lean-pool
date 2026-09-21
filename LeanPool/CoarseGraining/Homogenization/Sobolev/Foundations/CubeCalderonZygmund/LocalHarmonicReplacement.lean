/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.H10Adjoint
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-! # Local Harmonic Replacement -/

namespace Homogenization

open MeasureTheory

noncomputable section

namespace CubeCalderonZygmund

/-!
# Local harmonic replacement on axis cubes

This file constructs the zero-trace correction for a scalar constant-coefficient
divergence equation.  Subtracting the correction from the original function
produces a harmonic remainder, while direct testing by the correction gives the
dimension-free Hilbert-vector energy estimate used in the good-lambda argument.
-/

/-- A local scalar divergence equation on an axis cube admits a zero-trace
correction with the same equation.  The remainder is harmonic, and the
correction has the sharp Hilbert-vector energy bound with no dimension loss. -/
theorem exists_local_harmonic_replacement_axisCube
    {d : ℕ} [NeZero d] (z : Vec d) {L sigma0 : ℝ}
    (hL : 0 < L) (hsigma0 : 0 < sigma0)
    (u : H1Function (axisCube z L)) {h : Vec d → Vec d}
    (hh : MemVectorL2 (axisCube z L) h)
    (hweak :
      ∀ φ : Vec d → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ →
        tsupport φ ⊆ axisCube z L →
        sigma0 *
            ∫ x in axisCube z L,
              vecDot (u.grad x) (euclideanGradient φ x)
                ∂MeasureTheory.volume =
          -∫ x in axisCube z L,
              vecDot (h x) (euclideanGradient φ x)
                ∂MeasureTheory.volume) :
    ∃ w : H10Function (axisCube z L),
      (∀ ψ : H10Function (axisCube z L),
        sigma0 *
            ∫ x in axisCube z L,
              vecDot (w.toH1Function.grad x) (ψ.toH1Function.grad x)
                ∂MeasureTheory.volume =
          -∫ x in axisCube z L,
              vecDot (h x) (ψ.toH1Function.grad x)
                ∂MeasureTheory.volume) ∧
      WeakPoissonEquationOn (axisCube z L) (u - w.toH1Function) 0 ∧
      ‖w.toH1Function.gradToHilbertVectorL2‖ ≤
        sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hh‖ := by
  let U : Set (Vec d) := axisCube z L
  have hUgeom : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_axisCube z L
  obtain ⟨w, hw_divergence, hw_energy⟩ :=
    exists_axisCubeScalarDivergenceSolution z hL hsigma0 h hh
  have hharmonic : WeakPoissonEquationOn U (u - w.toH1Function) 0 := by
    intro φ hφ hφ_compact hφ_sub
    let ψ : H10Function U :=
      H10Function.ofContDiff hUgeom.isOpen hφ hφ_compact hφ_sub
    have hu_test :
        sigma0 *
            ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume =
          -∫ x in U, vecDot (h x) (euclideanGradient φ x)
              ∂MeasureTheory.volume := by
      simpa [U] using hweak φ hφ hφ_compact (by simpa [U] using hφ_sub)
    have hw_test :
        sigma0 *
            ∫ x in U,
              vecDot (w.toH1Function.grad x) (euclideanGradient φ x)
                ∂MeasureTheory.volume =
          -∫ x in U, vecDot (h x) (euclideanGradient φ x)
              ∂MeasureTheory.volume := by
      simpa [ψ, H10Function.ofContDiff, H1Function.ofContDiff,
        euclideanGradient, euclideanCoordDeriv] using! hw_divergence ψ
    have heq :
        ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume =
          ∫ x in U, vecDot (w.toH1Function.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume := by
      apply (mul_left_cancel₀ hsigma0.ne')
      exact hu_test.trans hw_test.symm
    have hu_int :
        IntegrableOn (fun x => vecDot (u.grad x) (euclideanGradient φ x)) U := by
      have hψgrad : ψ.toH1Function.grad = euclideanGradient φ := by
        rfl
      rw [← hψgrad]
      exact integrableOn_vecDot_of_memVectorL2
        u.grad_memVectorL2 ψ.toH1Function.grad_memVectorL2
    have hw_int :
        IntegrableOn
          (fun x => vecDot (w.toH1Function.grad x) (euclideanGradient φ x)) U := by
      have hψgrad : ψ.toH1Function.grad = euclideanGradient φ := by
        rfl
      rw [← hψgrad]
      exact integrableOn_vecDot_of_memVectorL2
        w.toH1Function.grad_memVectorL2 ψ.toH1Function.grad_memVectorL2
    calc
      ∫ x in U,
          vecDot ((u - w.toH1Function).grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume =
          ∫ x in U,
            (vecDot (u.grad x) (euclideanGradient φ x) -
              vecDot (w.toH1Function.grad x) (euclideanGradient φ x))
              ∂MeasureTheory.volume := by
            congr with x
            simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
      _ =
          (∫ x in U, vecDot (u.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume) -
            ∫ x in U,
              vecDot (w.toH1Function.grad x) (euclideanGradient φ x)
                ∂MeasureTheory.volume :=
        MeasureTheory.integral_sub hu_int hw_int
      _ = 0 := sub_eq_zero.mpr heq
      _ = ∫ x in U, (fun _ : Vec d => (0 : ℝ)) x * φ x
          ∂MeasureTheory.volume := by simp
  refine ⟨w, ?_, hharmonic, ?_⟩
  · simpa [U] using hw_divergence
  · simpa [U] using hw_energy

end CubeCalderonZygmund

end

end Homogenization
