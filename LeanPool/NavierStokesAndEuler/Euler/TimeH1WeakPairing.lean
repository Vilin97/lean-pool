/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeWeakDerivative
public import LeanPool.NavierStokesAndEuler.Euler.TimeH1PointwiseBounds

@[expose] public section

/-!
Integration by parts for an actual H¹ representative against zero-endpoint
tests. The identity follows from the proved primitive representation and
does not posit a weak derivative as an additional assumption.
-/

noncomputable section

namespace EulerTimeH1WeakPairing

open Set MeasureTheory InnerProductSpace EulerTimeLp EulerTerminalTimePrimitive
  EulerVolterraConvolution EulerTimeWeakDerivative EulerTimeH1PointwiseBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem inner_zero_trace (T : ℝ) (hT : 0 ≤ T) (p q : TimeLp T E)
    (η : ℝ → E) (hη : AbsolutelyContinuousOnInterval η 0 T)
    (hp : (p : ℝ → E) =ᵐ[timeMeasure T] η)
    (hder : ∀ᵐ t ∂timeMeasure T, HasDerivAt η (q t) t)
    (v : TimeLp T E) (hv : initialTrace T hT v = 0) :
    ⟪p,v⟫_ℝ = -⟪q,primitiveTimeLp T hT v⟫_ℝ := by
  have he : p = primitiveTimeLp T hT q+constantField T hT (η T) := by
    apply Lp.ext
    filter_upwards [hp,primitiveTimeLp_ae T hT q,constantField_ae T hT (η T),
      Lp.coeFn_add (primitiveTimeLp T hT q) (constantField T hT (η T)),
      ae_restrict_mem measurableSet_Icc] with t hpt hqt hct hat hmem
    rw [hpt,hat,Pi.add_apply,hqt,hct]
    exact eq_primitive_add_terminal T hT q η hη hder t hmem
  rw [he,inner_add_left,primitive_inner_zero_trace T hT q v hv,
    constantField_inner,hv,inner_zero_right,neg_zero,add_zero]

/-- A continuous derivative on the closed interval gives the exact weak
pairing of the corresponding genuine time L² elements. -/
theorem pathLp_inner_zero_trace (T : ℝ) (hT : 0 ≤ T)
    (p q : C(Icc (0 : ℝ) T,E))
    (hd : ∀ t : Icc (0 : ℝ) T,
      HasDerivWithinAt (extendPath T hT p) (q t) (Icc (0 : ℝ) T) t)
    (v : TimeLp T E) (hv : initialTrace T hT v = 0) :
    ⟪pathLp T hT p,v⟫_ℝ = -⟪pathLp T hT q,primitiveTimeLp T hT v⟫_ℝ := by
  have hac : AbsolutelyContinuousOnInterval (extendPath T hT p) 0 T := by
    have hl : LipschitzOnWith ‖q‖₊ (extendPath T hT p) (Icc (0 : ℝ) T) := by
      apply (convex_Icc (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (f' := extendPath T hT q)
      · intro t ht
        simpa only [extendPath,projIcc_of_mem hT ht] using hd ⟨t,ht⟩
      · intro t ht
        exact q.norm_coe_le_norm (projIcc 0 T hT t)
    exact (show LipschitzOnWith ‖q‖₊ (extendPath T hT p) (uIcc (0 : ℝ) T) by
      simpa only [uIcc_of_le hT] using hl).absolutelyContinuousOnInterval
  apply inner_zero_trace T hT (pathLp T hT p) (pathLp T hT q)
    (extendPath T hT p) hac (pathLp_ae T hT p) _ v hv
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ioo (0 : ℝ) T := by
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T), t ∈ Ioo (0 : ℝ) T
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem,pathLp_ae T hT q] with t ht hq
  have hti : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le,ht.2.le⟩
  rw [hq]
  simpa only [extendPath,projIcc_of_mem hT hti] using
    (hd ⟨t,hti⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end EulerTimeH1WeakPairing
