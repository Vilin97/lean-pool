/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceForwardCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.SmoothCoefficientPathMap

@[expose] public section

/-!
# The actual scalar normal coefficient as a one-column Gram inverse

The column r↦r m has Gram matrix ‖m‖². Its genuinely constructed bounded-field
left inverse is therefore exactly v↦⟪m,v⟫/‖m‖². This derives uniform time-space
regularity and factorial multiplier bounds from the normal field and its
positive lower bound, without assuming regularity of a reciprocal field.
-/

noncomputable section

namespace EulerSourceNormalCoefficient

open Set ContinuousLinearMap InnerProductSpace EulerSmoothLimit EulerMeanCoefficients
  EulerSourceForwardCoefficient EulerTransverseGramInverse EulerTimeLpGramGevrey EulerGevrey
open scoped BoundedContinuousFunction ContDiff

variable {K E : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (m : SmoothCoefficientPath K E)

/-- The normal vector as a genuine scalar-to-vector coefficient path. -/
def normalColumn : SmoothCoefficientPath K (ℝ →L[ℝ] E) :=
  SmoothCoefficientPath.map
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).toLinearIsometry.toContinuousLinearMap m

omit [CompleteSpace E] in
@[simp] theorem normalColumn_apply (t : K) (x : Space) (r : ℝ) :
    (normalColumn m).field t x r = r • m.field t x := rfl

omit [CompleteSpace E] in
theorem normalColumn_lower (c : ℝ) (hm : ∀ t x, c ≤ ‖m.field t x‖^2)
    (t : K) (x : Space) (r : ℝ) :
    c*‖r‖^2 ≤ ‖(normalColumn m).field t x r‖^2 := by
  rw [normalColumn_apply,norm_smul,mul_pow]
  exact (mul_le_mul_of_nonneg_right (hm t x) (sq_nonneg ‖r‖)).trans_eq (mul_comm _ _)

variable (c : ℝ) (hc : 0 < c) (hm : ∀ t x, c ≤ ‖m.field t x‖^2)

/-- The actual scalar coefficient used by the pressure in equation (11). -/
def normalFunctional : C(K,Space →ᵇ E →L[ℝ] ℝ) :=
  sourceForcing (normalColumn m) c hc (normalColumn_lower m c hm)

/-- The constructed Gram left inverse is precisely the literal normal quotient. -/
theorem normalFunctional_apply (t : K) (x : Space) (v : E) :
    normalFunctional m c hc hm t x v = ⟪m.field t x,v⟫_ℝ / ‖m.field t x‖^2 := by
  have hn : ‖m.field t x‖^2 ≠ 0 := ne_of_gt (hc.trans_le (hm t x))
  have he := gram_inverse_apply ((normalColumn m).field t x) c hc (normalColumn_lower m c hm t x)
    (((normalColumn m).field t x).adjoint v)
  change ((normalColumn m).field t x).adjoint
    ((normalColumn m).field t x (normalFunctional m c hc hm t x v)) =
      ((normalColumn m).field t x).adjoint v at he
  have hadj : ((normalColumn m).field t x).adjoint = innerSL ℝ (m.field t x) :=
    adjoint_toSpanSingleton (m.field t x)
  rw [hadj] at he
  change ⟪m.field t x,(normalFunctional m c hc hm t x v) • m.field t x⟫_ℝ =
    ⟪m.field t x,v⟫_ℝ at he
  rw [inner_smul_right,real_inner_self_eq_norm_sq] at he
  exact (eq_div_iff hn).2 he

/-- The pressure coefficient has genuine translated uniform-path regularity. -/
theorem normalFunctional_translation_contDiff :
    ContDiff ℝ ∞ (translateCoefficientPath (normalFunctional m c hc hm)) :=
  sourceForcing_translation_contDiff (normalColumn m) c hc (normalColumn_lower m c hm)

theorem normalFunctional_translation_bound
    (Rc C Ri : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C)
    (hRi : 2*gramCost c C 1*(Rc+1) ≤ Ri)
    (hbm : ∀ n t x, ‖iteratedFDeriv ℝ n (m.field t : Space → E) x‖ ≤ C*majorant Rc 0 n)
    (n : ℕ) (a : Space) :
    ‖iteratedFDeriv ℝ n (translateCoefficientPath (normalFunctional m c hc hm)) a‖ ≤
      (3*Ri*C)*majorant (4*Ri) 0 n := by
  apply sourceForcing_translation_bound (normalColumn m) c hc (normalColumn_lower m c hm)
    Rc C Ri hRc hC hRi _ n a
  intro j t x
  exact SmoothCoefficientPath.map_derivative_bound
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).toLinearIsometry.toContinuousLinearMap
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).toLinearIsometry.norm_toContinuousLinearMap_le
    m j (C*majorant Rc 0 j) (hbm j) t x

end EulerSourceNormalCoefficient
