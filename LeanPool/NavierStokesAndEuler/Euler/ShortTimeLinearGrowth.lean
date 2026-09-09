/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearFundamentalExistence

@[expose] public section

/-! A short-interval estimate for actual differentiable trajectories.
The proof uses the supremum norm and the mean value inequality, so the
constant is two under the stated smallness condition. -/

noncomputable section

namespace EulerShortTimeLinearGrowth

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_two (T L : ℝ) (hL : 0 ≤ L)
    (f f' : ℝ → E)
    (hd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt f (f' t) (Icc (0 : ℝ) T) t)
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ‖f' t‖ ≤ L*‖f t‖)
    (hshort : L*T ≤ 1/2)
    (s t : Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖f t‖ ≤ 2*‖f s‖ := by
  have hT : 0 ≤ T := s.property.1.trans s.property.2
  have hsub : Icc (s : ℝ) T ⊆ Icc (0 : ℝ) T :=
    fun _ hr => ⟨s.property.1.trans hr.1,hr.2⟩
  have hd' (r : ℝ) (hr : r ∈ Icc (s : ℝ) T) :
      HasDerivWithinAt f (f' r) (Icc (s : ℝ) T) r :=
    (hd r (hsub hr)).mono hsub
  have hc : ContinuousOn f (Icc (s : ℝ) T) :=
    fun r hr => (hd' r hr).continuousWithinAt
  let V : C(Icc (s : ℝ) T,E) :=
    ⟨fun r => f r,continuousOn_iff_continuous_domRestrict.mp hc⟩
  have hnorm (r : ℝ) (hr : r ∈ Icc (s : ℝ) T) : ‖f' r‖ ≤ L*‖V‖ :=
    (hb r (hsub hr)).trans
      (mul_le_mul_of_nonneg_left (V.norm_coe_le_norm ⟨r,hr⟩) hL)
  have hpoint (u : Icc (s : ℝ) T) :
      ‖V u‖ ≤ ‖f s‖+(L*T)*‖V‖ := by
    have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := L*‖V‖)
      hd' hnorm (convex_Icc (s : ℝ) T) (show (s : ℝ) ∈ Icc (s : ℝ) T from
        ⟨le_rfl,s.property.2⟩) u.property
    have hdist : ‖(u : ℝ)-(s : ℝ)‖ ≤ T := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr u.property.1)]
      linarith [s.property.1,u.property.2]
    have hdiff : ‖f u-f s‖ ≤ (L*T)*‖V‖ :=
      hh.trans ((mul_le_mul_of_nonneg_left hdist (mul_nonneg hL (norm_nonneg V))).trans_eq
        (by ring))
    calc
      ‖V u‖ = ‖(f u-f s)+f s‖ := by simp only [sub_add_cancel]; rfl
      _ ≤ ‖f u-f s‖+‖f s‖ := norm_add_le _ _
      _ ≤ (L*T)*‖V‖+‖f s‖ := add_le_add hdiff le_rfl
      _ = ‖f s‖+(L*T)*‖V‖ := add_comm _ _
  have hV : ‖V‖ ≤ ‖f s‖+(L*T)*‖V‖ :=
    (ContinuousMap.norm_le V (by positivity)).mpr hpoint
  have hsmall := mul_le_mul_of_nonneg_right hshort (norm_nonneg V)
  have hV' : ‖V‖ ≤ 2*‖f s‖ := by linarith
  exact (V.norm_coe_le_norm ⟨t,hst,t.property.2⟩).trans hV'

end EulerShortTimeLinearGrowth
