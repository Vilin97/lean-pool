/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Scalar closure of the whole-space comparison estimate

The localized energy may have derivatives only in the interior of the time
interval. The integrating-factor argument below therefore uses continuity on
the closed interval and the mean-value theorem on its interior. In particular,
no energy inequality at a time endpoint is assumed.
-/

@[expose] public section



noncomputable section

open Set

namespace NavierStokesR3.ComparisonGronwall

/-- The weighted perturbed Gronwall estimate with a nonpositive initial value.
Only interior derivatives of `E` are needed. -/
theorem exp_neg_mul_le_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, Real.exp (-K * t) * E t ≤ ε * t := by
  let G : ℝ → ℝ := fun t => Real.exp (-K * t) * E t - ε * t
  let G' : ℝ → ℝ := fun t => Real.exp (-K * t) * (E' t - K * E t) - ε
  have hgcont : ContinuousOn G (Icc 0 T) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      hcont).sub (continuous_const.mul continuous_id).continuousOn
  have hgderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt G (G' t) t := by
    have hexp := ((hasDerivAt_id t).const_mul (-K)).exp
    convert! (hexp.mul (hderiv t ht)).sub ((hasDerivAt_id t).const_mul ε) using 1
    try dsimp [G, G']
    ring
  have hG : AntitoneOn G (Icc 0 T) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hgcont
    · intro t ht
      exact (hgderiv t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo 0 T := by simpa only [interior_Icc] using ht
      have hexp : Real.exp (-K * t) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) ht'.1.le)
      have hfirst : Real.exp (-K * t) * (E' t - K * E t) ≤
          Real.exp (-K * t) * ε :=
        mul_le_mul_of_nonneg_left (by linarith [hbound t ht']) (Real.exp_pos _).le
      have hsecond : Real.exp (-K * t) * ε ≤ ε := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hexp hε
      dsimp only [G']
      linarith
  intro t ht
  have hle := hG ⟨le_rfl, hT⟩ ht ht.1
  have hzero : G 0 ≤ 0 := by simpa [G] using hinitial
  have hnonpos := hle.trans hzero
  exact sub_nonpos.mp hnonpos

/-- Perturbed Gronwall, retaining the actual time in the bound. -/
theorem le_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * t * Real.exp (K * t) := by
  intro t ht
  have hweighted := exp_neg_mul_le_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht
  have hmul := mul_le_mul_of_nonneg_right hweighted (Real.exp_pos (K * t)).le
  have hexp : Real.exp (-K * t) * Real.exp (K * t) = 1 := by
    rw [← Real.exp_add]
    have hcancel : -K * t + K * t = 0 := by ring
    rw [hcancel, Real.exp_zero]
  calc
    E t = Real.exp (-K * t) * E t * Real.exp (K * t) := by
      calc
        E t = E t * 1 := (mul_one _).symm
        _ = E t * (Real.exp (-K * t) * Real.exp (K * t)) := by rw [hexp]
        _ = _ := by ring
    _ ≤ ε * t * Real.exp (K * t) := hmul

/-- Perturbed Gronwall with one bound valid throughout the closed interval. -/
theorem le_uniform_exp_mul_of_deriv_le {T K ε : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + ε) :
    ∀ t ∈ Icc 0 T, E t ≤ ε * T * Real.exp (K * T) := by
  intro t ht
  calc
    E t ≤ ε * t * Real.exp (K * t) :=
      le_exp_mul_of_deriv_le hT hK hε hcont hinitial hderiv hbound t ht
    _ ≤ ε * T * Real.exp (K * T) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left ht.2 hε
      · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
      · exact (Real.exp_pos _).le
      · exact mul_nonneg hε hT

/-- A forcing error of order `1 / R` gives a uniform energy error of the same
order. The numerator depends only on `C`, `K`, and the time interval. -/
theorem le_div_radius_of_deriv_le {T K C R : ℝ} {E E' : ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C) (hR : 0 < R)
    (hcont : ContinuousOn E (Icc 0 T)) (hinitial : E 0 = 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hbound : ∀ t ∈ Ioo 0 T, E' t ≤ K * E t + C / R) :
    ∀ t ∈ Icc 0 T, E t ≤ (C * T * Real.exp (K * T)) / R := by
  intro t ht
  have hle := le_uniform_exp_mul_of_deriv_le hT hK (div_nonneg hC hR.le)
    hcont hinitial.le hderiv hbound t ht
  convert! hle using 1
  ring

/-- Apply the scalar estimate to a family of localized energies. All radii
share the same constant in the numerator. -/
theorem exists_uniform_radius_bound {T K C : ℝ} {E E' : ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hcont : ∀ R : ℝ, 1 ≤ R → ContinuousOn (E R) (Icc 0 T))
    (hinitial : ∀ R : ℝ, 1 ≤ R → E R 0 = 0)
    (hderiv : ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T, HasDerivAt (E R) (E' R t) t)
    (hbound : ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Ioo 0 T, E' R t ≤ K * E R t + C / R) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 1 ≤ R → ∀ t ∈ Icc 0 T, E R t ≤ D / R := by
  refine ⟨C * T * Real.exp (K * T), mul_nonneg (mul_nonneg hC hT) (Real.exp_pos _).le,
    ?_⟩
  intro R hR
  exact le_div_radius_of_deriv_le hT hK hC (lt_of_lt_of_le zero_lt_one hR)
    (hcont R hR) (hinitial R hR) (hderiv R hR) (hbound R hR)

/-- A nonnegative scalar with a uniform `1 / R` bound for every `R ≥ 1`
vanishes. This is the final scalar step in cutoff exhaustion. -/
theorem eq_zero_of_forall_radius_bound {x D : ℝ} (hx : 0 ≤ x) (hD : 0 ≤ D)
    (hbound : ∀ R : ℝ, 1 ≤ R → x ≤ D / R) : x = 0 := by
  by_contra hzero
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  let R : ℝ := (D + 1) / x + 1
  have hR : 1 ≤ R := by
    dsimp [R]
    linarith [div_nonneg (show 0 ≤ D + 1 by linarith) hx]
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hmul : x * R ≤ D := (le_div_iff₀ hRpos).mp (hbound R hR)
  have hcancel : (D + 1) / x * x = D + 1 := div_mul_cancel₀ _ hxpos.ne'
  dsimp [R] at hmul
  nlinarith

/-- For a fixed compact set, the cutoff bound is available only after the
radius contains that set. Such a bound is still sufficient for vanishing. -/
theorem eq_zero_of_forall_large_radius_bound {x D R₀ : ℝ} (hx : 0 ≤ x)
    (hbound : ∀ R : ℝ, max 1 R₀ ≤ R → x ≤ D / R) : x = 0 := by
  by_contra hzero
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
  let R : ℝ := max (max 1 R₀) ((D + 1) / x + 1)
  have hR : max 1 R₀ ≤ R := le_max_left _ _
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hR)
  have hmul : x * R ≤ D := (le_div_iff₀ hRpos).mp (hbound R hR)
  have hsize : (D + 1) / x + 1 ≤ R := le_max_right _ _
  have hsize_mul := mul_le_mul_of_nonneg_left hsize hx
  have hcancel : (D + 1) / x * x = D + 1 := div_mul_cancel₀ _ hxpos.ne'
  nlinarith

end NavierStokesR3.ComparisonGronwall
