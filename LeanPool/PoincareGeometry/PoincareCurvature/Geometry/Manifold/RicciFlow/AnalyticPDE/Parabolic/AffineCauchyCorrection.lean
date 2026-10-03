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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.Parametrix

/-!
# Affine correction of a zero-initial right inverse

If `Q` is a right inverse of an equation operator `P` and every value of `Q`
has zero trace, then

`h + Q (f - P h)`

solves the equation with forcing `f` and has the same trace as the chosen
extension `h`.  This elementary operator identity is the bridge from a
zero-initial parametrix to a Cauchy solver with nonzero initial data.
-/

@[expose] public noncomputable section

namespace RicciFlow
namespace AnalyticPDE
namespace LinearParabolicParametrix

variable {U F J : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

/-- Correct a chosen extension `h` by the zero-trace solution of its equation
defect.  For fixed `h` this is an affine, rather than linear, function of the
forcing. -/
def affineCauchyCorrection
    (P : U →L[ℝ] F) (Q : F →L[ℝ] U) (h : U) (f : F) : U :=
  h + Q (f - P h)

/-- The affine correction solves the prescribed equation whenever `Q` is a
right inverse of `P`. -/
theorem apply_affineCauchyCorrection
    (P : U →L[ℝ] F) (Q : F →L[ℝ] U)
    (hPQ : P.comp Q = ContinuousLinearMap.id ℝ F)
    (h : U) (f : F) :
    P (affineCauchyCorrection P Q h f) = f := by
  rw [affineCauchyCorrection, map_add, ← ContinuousLinearMap.comp_apply,
    hPQ]
  simp

/-- The affine correction retains the trace of the chosen extension whenever
the range of `Q` has zero trace. -/
theorem trace_affineCauchyCorrection
    (trace : U →L[ℝ] J) (P : U →L[ℝ] F) (Q : F →L[ℝ] U)
    (htrace : trace.comp Q = 0)
    (h : U) (f : F) :
    trace (affineCauchyCorrection P Q h f) = trace h := by
  rw [affineCauchyCorrection, map_add, ← ContinuousLinearMap.comp_apply,
    htrace]
  simp

/-- The direct Schauder-type bound for the affine correction. -/
theorem norm_affineCauchyCorrection_le
    (P : U →L[ℝ] F) (Q : F →L[ℝ] U) (h : U) (f : F) :
    ‖affineCauchyCorrection P Q h f‖ ≤
      ‖h‖ + ‖Q‖ * ‖f - P h‖ := by
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl (Q.le_opNorm (f - P h)))

/-- Existential form used by local and global Cauchy-problem interfaces. -/
theorem exists_solution_with_trace_of_rightInverse_zeroTrace
    (trace : U →L[ℝ] J) (P : U →L[ℝ] F) (Q : F →L[ℝ] U)
    (hPQ : P.comp Q = ContinuousLinearMap.id ℝ F)
    (htrace : trace.comp Q = 0)
    (h : U) (f : F) :
    ∃ u : U,
      P u = f ∧ trace u = trace h ∧
        ‖u‖ ≤ ‖h‖ + ‖Q‖ * ‖f - P h‖ := by
  refine ⟨affineCauchyCorrection P Q h f,
    apply_affineCauchyCorrection P Q hPQ h f,
    trace_affineCauchyCorrection trace P Q htrace h f,
    norm_affineCauchyCorrection_le P Q h f⟩

end LinearParabolicParametrix
end AnalyticPDE
end RicciFlow
