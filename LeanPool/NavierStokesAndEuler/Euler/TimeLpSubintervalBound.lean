/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import LeanPool.NavierStokesAndEuler.Euler.PDESubintervalEnergyLimit
import LeanPool.NavierStokesAndEuler.Euler.TimeLpSubinterval
import Mathlib.Algebra.Order.Star.Real

/-! Actual L² forcing bounds imply continuous scalar integral majorants on every time subinterval.
-/

@[expose] public section


noncomputable section

namespace EulerTimeLpSubintervalBound

open MeasureTheory Set InnerProductSpace EulerTimeLp EulerVolterraConvolution EulerTimeLpSubinterval
  EulerPDESubintervalEnergyLimit

/-- Two genuine real L² time fields have an integrable product. -/
theorem integrable_time_product (T : ℝ) (u v : TimeLp T ℝ) :
    Integrable (fun t => u t*v t) (timeMeasure T) := by
  have h := L2.integrable_inner (𝕜 := ℝ) u v
  simpa only [RCLike.inner_apply, conj_trivial, mul_comm] using h

/-- A genuine almost-everywhere forcing bound gives its signed coefficient comparison on every time
subinterval. -/
theorem subinterval_forcing_bound (T : ℝ) (hT : 0 ≤ T) (s t : ℝ)
    (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (k g : C(Icc (0 : ℝ) T, ℝ)) (hk : ∀ r, 0 ≤ k r) (F : TimeLp T ℝ)
    (hF : (F : ℝ → ℝ) ≤ᵐ[timeMeasure T] extendPath T hT g) :
    (∫ r in Icc s t, pathLp T hT k r*F r ∂timeMeasure T) ≤
      ∫ r in s..t, extendPath T hT k r*extendPath T hT g r := by
  have hi := (integrable_time_product T (pathLp T hT k) F).restrict (s := Icc s t)
  have hj := (integrable_time_product T (pathLp T hT k) (pathLp T hT g)).restrict (s := Icc s t)
  have h := integral_mono_ae hi hj (show
      (fun r => pathLp T hT k r*F r) ≤ᵐ[(timeMeasure T).restrict (Icc s t)]
        (fun r => pathLp T hT k r*pathLp T hT g r) from by
    filter_upwards [ae_restrict_of_ae hF, ae_restrict_of_ae (pathLp_ae T hT k),
      ae_restrict_of_ae (pathLp_ae T hT g)] with r hr hkr hgr
    rw [hkr,hgr]
    exact mul_le_mul_of_nonneg_left hr (hk (projIcc 0 T hT r)))
  have he := (subinterval_inner_eq T s t (pathLp T hT k) (pathLp T hT g)).symm.trans
    (subinterval_path_inner T hT s t h0s hst htT k g)
  exact h.trans_eq he

/-- The actual continuous scalar right-hand side after an almost-everywhere forcing estimate. -/
def scalarEnergyRhs (T : ℝ) (a b k X Y F : C(Icc (0 : ℝ) T, ℝ)) : C(Icc (0 : ℝ) T, ℝ) :=
  a*X+b*Y+k*F

/-- Passing the actual forcing estimate through the integral yields a continuous scalar energy
majorant. -/
theorem scalar_rhs_subinterval (T : ℝ) (hT : 0 ≤ T) (s t : ℝ)
    (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (a b k X Y g : C(Icc (0 : ℝ) T, ℝ)) (hk : ∀ r, 0 ≤ k r) (F : TimeLp T ℝ)
    (hF : (F : ℝ → ℝ) ≤ᵐ[timeMeasure T] extendPath T hT g)
    (he : X ⟨t, h0s.trans hst, htT⟩ - X ⟨s, h0s, hst.trans htT⟩ ≤
      (∫ r in s..t, extendPath T hT a r * extendPath T hT X r) +
      (∫ r in s..t, extendPath T hT b r * extendPath T hT Y r) +
      ∫ r in Icc s t, pathLp T hT k r * F r ∂timeMeasure T) :
    X ⟨t,h0s.trans hst,htT⟩-X ⟨s,h0s,hst.trans htT⟩ ≤
      ∫ r in s..t, extendPath T hT (scalarEnergyRhs T a b k X Y g) r := by
  have h := he.trans (add_le_add (le_refl _) (subinterval_forcing_bound T hT s t h0s hst htT k g hk
      F hF))
  have hi := integral_eq_three_subinterval_paths T hT s t hst a b k X Y g
    (extendPath T hT (scalarEnergyRhs T a b k X Y g)) (fun _ _ => rfl)
  exact h.trans_eq hi.symm

end EulerTimeLpSubintervalBound
