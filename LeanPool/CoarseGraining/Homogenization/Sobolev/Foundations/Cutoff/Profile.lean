/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

/-! # Profile -/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Homogenization

/-!
# One-dimensional smooth cutoff profiles

This file isolates the one-dimensional analytic input for quantitative cutoff
constructions.  The geometric ball and cube cutoffs should depend only on a
profile carrying explicit first- and second-derivative bounds.
-/

/-- A smooth transition profile with certified quantitative first and second
derivative bounds.

The intended use is:

* `θ t = 0` for `t ≤ 0`;
* `θ t = 1` for `1 ≤ t`;
* `0 ≤ θ ≤ 1`;
* `‖θ'‖∞ ≤ derivBound`;
* `‖θ''‖∞ ≤ secondDerivBound`.

Keeping these constants in the profile avoids burying the hard one-dimensional
analysis inside the ball and cube cutoff proofs. -/
structure QuantitativeTransitionProfile where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  zero_of_nonpos : ∀ {t : ℝ}, t ≤ 0 → toFun t = 0
  one_of_one_le : ∀ {t : ℝ}, 1 ≤ t → toFun t = 1
  nonneg : ∀ t, 0 ≤ toFun t
  le_one : ∀ t, toFun t ≤ 1
  derivBound : ℝ
  derivBound_nonneg : 0 ≤ derivBound
  norm_deriv_le : ∀ t, ‖deriv toFun t‖ ≤ derivBound
  secondDerivBound : ℝ
  secondDerivBound_nonneg : 0 ≤ secondDerivBound
  norm_secondDeriv_le : ∀ t, ‖deriv (deriv toFun) t‖ ≤ secondDerivBound

namespace QuantitativeTransitionProfile

instance : CoeFun QuantitativeTransitionProfile (fun _ => ℝ → ℝ) where
  coe θ := θ.toFun

end QuantitativeTransitionProfile

/-- The canonical smooth transition supplied by mathlib.  This is the natural
explicit formula to analyze:
`exp(-1/t) / (exp(-1/t) + exp(-1/(1-t)))`, with the endpoint extensions from
`Real.expNegInvGlue`.

The basic shape facts are already in mathlib; the quantitative derivative
bounds are the remaining one-dimensional project. -/
def smoothTransitionProfile (t : ℝ) : ℝ :=
  Real.smoothTransition t

namespace smoothTransitionProfile

theorem smooth : ContDiff ℝ (⊤ : ℕ∞) smoothTransitionProfile :=
  Real.smoothTransition.contDiff

theorem zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    smoothTransitionProfile t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

theorem one_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    smoothTransitionProfile t = 1 :=
  Real.smoothTransition.one_of_one_le ht

theorem nonneg (t : ℝ) : 0 ≤ smoothTransitionProfile t :=
  Real.smoothTransition.nonneg t

theorem le_one (t : ℝ) : smoothTransitionProfile t ≤ 1 :=
  Real.smoothTransition.le_one t

theorem pos_of_pos {t : ℝ} (ht : 0 < t) :
    0 < smoothTransitionProfile t :=
  Real.smoothTransition.pos_of_pos ht

theorem differentiable : Differentiable ℝ smoothTransitionProfile :=
  smooth.differentiable (by simp)

/-- The derivative of the smooth transition vanishes on the open zero side. -/
theorem deriv_zero_of_neg {t : ℝ} (ht : t < 0) :
    deriv smoothTransitionProfile t = 0 := by
  have h : smoothTransitionProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    exact zero_of_nonpos hy.le
  exact h.deriv_eq.trans (deriv_const t (0 : ℝ))

/-- The derivative of the smooth transition vanishes on the open one side. -/
theorem deriv_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv smoothTransitionProfile t = 0 := by
  have h : smoothTransitionProfile =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact one_of_one_le hy.le
  exact h.deriv_eq.trans (deriv_const t (1 : ℝ))

private theorem secondDeriv_zero_of_neg {t : ℝ} (ht : t < 0) :
    deriv (deriv smoothTransitionProfile) t = 0 := by
  have h : deriv smoothTransitionProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds ht] with y hy
    exact deriv_zero_of_neg hy
  exact h.deriv_eq.trans (deriv_const t (0 : ℝ))

private theorem secondDeriv_zero_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv (deriv smoothTransitionProfile) t = 0 := by
  have h : deriv smoothTransitionProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact deriv_zero_of_one_lt hy
  exact h.deriv_eq.trans (deriv_const t (0 : ℝ))

theorem continuous_deriv : Continuous (deriv smoothTransitionProfile) :=
  (smooth.of_le (by simp)).continuous_deriv_one

/-- The derivative of the smooth transition vanishes on the closed zero side.

The endpoint follows from continuity of the derivative and the open-side
identity. -/
theorem deriv_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    deriv smoothTransitionProfile t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact deriv_zero_of_neg ht
  have hleft_eq :
      deriv smoothTransitionProfile =ᶠ[𝓝[<] (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact deriv_zero_of_neg hy
  have hleft_tendsto :
      Tendsto (deriv smoothTransitionProfile) (𝓝[<] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hleft_eq.tendsto
  have hcont_tendsto :
      Tendsto (deriv smoothTransitionProfile) (𝓝[<] (0 : ℝ))
        (𝓝 (deriv smoothTransitionProfile (0 : ℝ))) :=
    continuous_deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique hleft_tendsto hcont_tendsto).symm

/-- The derivative of the smooth transition vanishes on the closed one side.

The endpoint follows from continuity of the derivative and the open-side
identity. -/
theorem deriv_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv smoothTransitionProfile t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact deriv_zero_of_one_lt ht
  have hright_eq :
      deriv smoothTransitionProfile =ᶠ[𝓝[>] (1 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact deriv_zero_of_one_lt hy
  have hright_tendsto :
      Tendsto (deriv smoothTransitionProfile) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) :=
    hright_eq.tendsto
  have hcont_tendsto :
      Tendsto (deriv smoothTransitionProfile) (𝓝[>] (1 : ℝ))
        (𝓝 (deriv smoothTransitionProfile (1 : ℝ))) :=
    continuous_deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact (tendsto_nhds_unique hright_tendsto hcont_tendsto).symm

theorem contDiff_deriv : ContDiff ℝ (⊤ : ℕ∞) (deriv smoothTransitionProfile) := by
  simpa using
    (ContDiff.iterate_deriv (𝕜 := ℝ) (F := ℝ) 1
      (f := smoothTransitionProfile) smooth)

theorem continuous_secondDeriv : Continuous (deriv (deriv smoothTransitionProfile)) := by
  have h : ContDiff ℝ (1 : ℕ∞) (deriv smoothTransitionProfile) :=
    contDiff_deriv.of_le (by simp)
  exact h.continuous_deriv_one

private theorem exists_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ‖deriv smoothTransitionProfile t‖ ≤ C := by
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) continuous_deriv.norm.continuousOn
  refine ⟨‖deriv smoothTransitionProfile M‖, norm_nonneg _, fun t => ?_⟩
  by_cases ht0 : t < 0
  · rw [deriv_zero_of_neg ht0, norm_zero]
    exact norm_nonneg _
  · by_cases ht1 : 1 < t
    · rw [deriv_zero_of_one_lt ht1, norm_zero]
      exact norm_nonneg _
    · push Not at ht0 ht1
      exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)

private theorem exists_secondDeriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖deriv (deriv smoothTransitionProfile) t‖ ≤ C := by
  obtain ⟨M, -, hM_max⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) continuous_secondDeriv.norm.continuousOn
  refine ⟨‖deriv (deriv smoothTransitionProfile) M‖, norm_nonneg _, fun t => ?_⟩
  by_cases ht0 : t < 0
  · rw [secondDeriv_zero_of_neg ht0, norm_zero]
    exact norm_nonneg _
  · by_cases ht1 : 1 < t
    · rw [secondDeriv_zero_of_one_lt ht1, norm_zero]
      exact norm_nonneg _
    · push Not at ht0 ht1
      exact Filter.eventually_principal.mp hM_max t (Set.mem_Icc.2 ⟨ht0, ht1⟩)

/-- Noncomputable global first-derivative bound for `smoothTransitionProfile`.

This is proved by compactness.  It is intentionally separated from the later
project of proving a small explicit numerical bound. -/
noncomputable def derivBound : ℝ :=
  Classical.choose (show ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖deriv smoothTransitionProfile t‖ ≤ C from by exact exists_deriv_bound)

theorem derivBound_nonneg : 0 ≤ derivBound :=
  exists_deriv_bound.choose_spec.1

theorem norm_deriv_le (t : ℝ) :
    ‖deriv smoothTransitionProfile t‖ ≤ derivBound :=
  exists_deriv_bound.choose_spec.2 t

/-- Noncomputable global second-derivative bound for `smoothTransitionProfile`. -/
noncomputable def secondDerivBound : ℝ :=
  Classical.choose (show ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, ‖deriv (deriv smoothTransitionProfile) t‖ ≤ C from by
    exact exists_secondDeriv_bound)

theorem secondDerivBound_nonneg : 0 ≤ secondDerivBound :=
  exists_secondDeriv_bound.choose_spec.1

theorem norm_secondDeriv_le (t : ℝ) :
    ‖deriv (deriv smoothTransitionProfile) t‖ ≤ secondDerivBound :=
  exists_secondDeriv_bound.choose_spec.2 t

/-- `Real.smoothTransition` packaged as a quantitative transition profile, with
noncomputable compactness bounds for the first and second derivatives. -/
def quantitativeProfile : QuantitativeTransitionProfile where
  toFun := smoothTransitionProfile
  smooth := smooth
  zero_of_nonpos := zero_of_nonpos
  one_of_one_le := one_of_one_le
  nonneg := nonneg
  le_one := le_one
  derivBound := derivBound
  derivBound_nonneg := derivBound_nonneg
  norm_deriv_le := norm_deriv_le
  secondDerivBound := secondDerivBound
  secondDerivBound_nonneg := secondDerivBound_nonneg
  norm_secondDeriv_le := norm_secondDeriv_le

end smoothTransitionProfile

end Homogenization
