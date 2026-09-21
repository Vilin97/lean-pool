/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The squared norm of Ricci curvature

This file defines the pointwise Hilbert--Schmidt square of the Ricci tensor
and proves the trace inequality

`R² ≤ n |Ric|²`.

This is the algebraic estimate that turns the exact scalar-curvature
evolution equation into the quadratic lower-barrier inequality.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

variable {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov.ContMDiffCovariantDerivative 1]

/-- The pointwise Hilbert--Schmidt square `|Ric|²`, evaluated in the standard
orthonormal basis of the tangent fibre. -/
def ricciNormSq (x : M) : ℝ := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E
      (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  exact ∑ i, ∑ j, (ricciCurvature (cov := cov) x (b i) (b j)) ^ 2

lemma ricciNormSq_eq_sum (x : M) :
    ricciNormSq (cov := cov) x =
      (by
        let _ : FiniteDimensional ℝ (TangentSpace I x) :=
          VectorBundle.finiteDimensional ℝ E
            (TangentSpace I : M → Type _) x
        let b := stdOrthonormalBasis ℝ (TangentSpace I x)
        exact ∑ i, ∑ j, (ricciCurvature (cov := cov) x (b i) (b j)) ^ 2) := by
  rfl

theorem ricciNormSq_nonneg (x : M) : 0 ≤ ricciNormSq (cov := cov) x := by
  rw [ricciNormSq_eq_sum]
  positivity

/-- The square of scalar curvature is at most dimension times the squared
Hilbert--Schmidt norm of Ricci curvature. -/
theorem scalarCurvature_sq_le_finrank_mul_ricciNormSq (x : M) :
    (scalarCurvature (cov := cov) x) ^ 2 ≤
      (Module.finrank ℝ (TangentSpace I x) : ℝ) *
        ricciNormSq (cov := cov) x := by
  let _ : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E
      (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [scalarCurvature_eq_sum, ricciNormSq_eq_sum]
  calc
    (∑ i, ricciCurvature (cov := cov) x (b i) (b i)) ^ 2 ≤
        (Fintype.card (Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) *
          ∑ i, (ricciCurvature (cov := cov) x (b i) (b i)) ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq
        (s := Finset.univ)
        (f := fun i : Fin (Module.finrank ℝ (TangentSpace I x)) =>
          ricciCurvature (cov := cov) x (b i) (b i))
    _ ≤ (Module.finrank ℝ (TangentSpace I x) : ℝ) *
          ∑ i, ∑ j, (ricciCurvature (cov := cov) x (b i) (b j)) ^ 2 := by
      simp only [Fintype.card_fin]
      gcongr with i
      exact Finset.single_le_sum (fun j _ => sq_nonneg
        (ricciCurvature (cov := cov) x (b i) (b j))) (Finset.mem_univ i)

end CovariantDerivative
