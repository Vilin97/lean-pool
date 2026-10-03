/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ConnectionChange
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci

/-!
# Ricci curvature under an affine connection change

This file contracts the pointwise curvature-change formula for
`CovariantDerivative.addOneForm` in an arbitrary orthonormal tangent frame.
The correction is kept as the explicit covariant derivative of the
endomorphism-valued one-form and its quadratic term; no remainder is hidden
behind a new definition.
-/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M ↦ TM x →L[ℝ] TM x →L[ℝ] TM x)

/-- The Ricci-curvature change formula in any orthonormal tangent frame.

For `∇' = ∇ + A`, the summand is the trace in the first/output curvature
slots of
`(∇_e A)(w,u) - (∇_u A)(w,e) + A(A(w,u),e) - A(A(w,e),u)`.
The argument order of `covariantDerivativeOneForm` is
`(derivative direction, differentiated vector, one-form direction)`.
-/
theorem ricciCurvature_addOneForm_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) [ContMDiffCovariantDerivative cov 1]
    (A : ∀ x : M, TCorr x) (hTorsionFree : cov.torsion = 0)
    (hA : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E))
        (E := TCorr) y (A y)))
    (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TM x)) (u w : TM x) :
    letI : ContMDiffCovariantDerivative (CovariantDerivative.addOneForm cov A) 1 :=
      ContMDiffCovariantDerivative.addOneForm (cov := cov) hA
    ricciCurvature (cov := CovariantDerivative.addOneForm cov A) x u w =
      ricciCurvature (cov := cov) x u w +
        ∑ i, inner ℝ (b i)
          (covariantDerivativeOneForm cov A x (b i) w u -
            covariantDerivativeOneForm cov A x u w (b i) +
              A x (A x w u) (b i) - A x (A x w (b i)) u) := by
  let _ : ContMDiffCovariantDerivative (CovariantDerivative.addOneForm cov A) 1 :=
    ContMDiffCovariantDerivative.addOneForm (cov := cov) hA
  have hAAt : ∀ y, MDiffAt
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) z (A z)) y := by
    intro y
    exact (hA y).mdifferentiableAt one_ne_zero
  rw [ricciCurvature_eq_sum_curvature_orthonormalBasis
      (CovariantDerivative.addOneForm cov A) x b,
    ricciCurvature_eq_sum_curvature_orthonormalBasis cov x b,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [curvatureTensor_addOneForm_apply cov A hTorsionFree hAAt x (b i) u w]
  simp only [inner_add_right, inner_sub_right]
  ring

end CovariantDerivative
