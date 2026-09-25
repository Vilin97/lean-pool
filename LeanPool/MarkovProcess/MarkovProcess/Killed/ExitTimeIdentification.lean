/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.Resolvent


/-!
# Identifying the expected exit time with a Dirichlet resolvent

The killed resolvent of the constant function one at the shift zero is the expected exit time,

  `E_x τ_U = R^U_0 1 (x)`  (`IsConservative.lintegral_exitTime_eq_killedResolvent_zero`),

and the shift zero is the increasing limit of the positive shifts `1 / (n + 1)`
(`IsConservative.killedResolvent_zero_eq_iSup`).  Both statements are unconditional.

Consumers who identify the killed resolvent at positive shifts with an analytically defined
Dirichlet resolvent `RU` then read the expected exit time off the limit of `RU`
(`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq`): the identification enters only as a
hypothesis, so nothing here depends on how it is established.  Two one-sided corollaries are
recorded, an upper bound from a uniform upper bound on the limit
(`IsConservative.lintegral_exitTime_le_of_killedResolvent_eq`) and a lower bound on a subset from a
uniform lower bound there (`IsConservative.le_lintegral_exitTime_of_killedResolvent_eq`).

The limit of `RU` enters those statements as a supremum along the shifts `1 / (n + 1)`.  A
consumer who instead has a limit as the shift decreases to zero converts it with
`IsConservative.iSup_eq_of_tendsto_nhdsGT_zero`: the killed resolvent is antitone in the shift, so
the identification makes `RU` antitone on `U` too and the sequence increases to its limit.

The consumer-supplied resolvent and its limit are `ℝ≥0∞`-valued, so no integrability or finiteness
hypothesis appears; a consumer working with real-valued solutions bridges with `ENNReal.ofReal`.
-/

@[expose] public section

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MarkovProcess.SubMarkovKernelSemigroup

section

/-- The exponential discounts at the shifts `1 / (n + 1)` increase to one on the nonnegative
half-line. -/
private theorem iSup_ofReal_exp_neg_inv_mul (t : ℝ) (ht : 0 ≤ t) :
    ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) = 1 := by
  have hmono : Monotone fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) := by
    intro m n hmn
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_right ?_ ht
    refine neg_le_neg ?_
    exact inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
  have hzero : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simp_rw [one_div] at h
    exact h
  have hlim : Tendsto (fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t))) atTop
      (𝓝 1) := by
    have hreal : Tendsto (fun n : ℕ ↦ Real.exp (-((n : ℝ) + 1)⁻¹ * t)) atTop
        (𝓝 (Real.exp (-(0 : ℝ) * t))) :=
      (Real.continuous_exp.tendsto _).comp (((hzero.neg).mul_const t))
    have h := ENNReal.tendsto_ofReal hreal
    simpa only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one] using h
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) hlim

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- **The expected exit time is the killed resolvent of one at the shift zero.** -/
theorem IsConservative.lintegral_exitTime_eq_killedResolvent_zero (U : Set alpha) (hU : IsOpen U)
    (x : alpha) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) =
      IsConservative.killedResolvent P hP U hU 0 (fun _ ↦ 1) x := by
  rw [IsConservative.killedResolvent_eq_lintegral P hP U hU 0 (f := fun _ ↦ (1 : ℝ≥0∞))
    measurable_const x]
  refine lintegral_congr fun omega ↦ ?_
  set tau : ℝ≥0∞ := ContinuousPath.exitTime U omega with htau
  have hS : MeasurableSet {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp measurable_real_toNNReal)
      measurable_const
  have hinner : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-0 * t)) *
      {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) t) =
      volume ({t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau} ∩ Set.Ioi 0) := by
    have hpoint : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-0 * t)) *
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) t =
        {t : ℝ | ((Real.toNNReal t : NNReal) : ℝ≥0∞) < tau}.indicator
          (fun _ ↦ (1 : ℝ≥0∞)) t := by
      intro t
      simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
    rw [lintegral_congr hpoint, lintegral_indicator hS, setLIntegral_one,
      Measure.restrict_apply hS]
  rw [hinner, ContinuousPath.survivalSet tau]
  by_cases htop : tau = ⊤
  · rw [ite_eq_left htop, htop, Real.volume_Ioi]
  · rw [ite_eq_right htop, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal htop]

/-- The killed resolvent at the shift zero is the increasing limit of the killed resolvents at the
positive shifts `1 / (n + 1)`. -/
theorem IsConservative.killedResolvent_zero_eq_iSup (U : Set alpha) (hU : IsOpen U)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    IsConservative.killedResolvent P hP U hU 0 f x =
      ⨆ n : ℕ, IsConservative.killedResolvent P hP U hU ((n : ℝ) + 1)⁻¹ f x := by
  set G : ℝ → ℝ≥0∞ := fun t ↦
    ∫⁻ y, f y ∂(IsConservative.killedKernel P hP U hU (Real.toNNReal t) x) with hG
  have hGmeas : Measurable G := by
    refine (Measure.measurable_lintegral hf).comp ?_
    exact (IsConservative.measurable_killedKernel P hP U hU).comp
      (measurable_real_toNNReal.prodMk measurable_const)
  have hFmeas : ∀ n : ℕ,
      Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t := by
    intro n
    exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_id))).mul hGmeas
  have hFmono : ∀ t ∈ Set.Ioi (0 : ℝ),
      Monotone fun n : ℕ ↦ ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t := by
    intro t ht m n hmn
    refine mul_le_mul_left ?_ (G t)
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_right (neg_le_neg ?_) (le_of_lt ht)
    exact inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
  have hkey : ∀ t ∈ Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-0 * t)) * G t =
      ⨆ n : ℕ, ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t := by
    intro t ht
    rw [← ENNReal.iSup_mul, iSup_ofReal_exp_neg_inv_mul t (le_of_lt ht)]
    simp only [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one]
  calc
    IsConservative.killedResolvent P hP U hU 0 f x =
        ∫⁻ t in Set.Ioi (0 : ℝ), ⨆ n : ℕ,
          ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t :=
      setLIntegral_congr_fun measurableSet_Ioi hkey
    _ = ⨆ n : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-((n : ℝ) + 1)⁻¹ * t)) * G t :=
      lintegral_iSup' (fun n ↦ (hFmeas n).aemeasurable)
        (ae_restrict_of_forall_mem measurableSet_Ioi hFmono)
    _ = ⨆ n : ℕ, IsConservative.killedResolvent P hP U hU ((n : ℝ) + 1)⁻¹ f x := rfl

variable (RU : ℝ → alpha → ℝ≥0∞) (w : alpha → ℝ≥0∞)

/-- **A limit as the shift decreases to zero is the supremum along `1 / (n + 1)`.**  The killed
resolvent is antitone in the shift, so a family `RU` agreeing with it on `U` at every positive
shift is antitone there as well, and a limit of `RU` as the shift decreases to zero is therefore
the supremum of the sequence.  This produces the hypothesis `hlim` of
`IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq` from the limit a consumer usually
has. -/
theorem IsConservative.iSup_eq_of_tendsto_nhdsGT_zero (U : Set alpha) (hU : IsOpen U)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hw : ∀ y ∈ U, Tendsto (fun lam : ℝ ↦ RU lam y) (𝓝[>] (0 : ℝ)) (𝓝 (w y))) :
    ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y := by
  intro y hy
  have hpos : ∀ n : ℕ, (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := fun n ↦ by positivity
  have hmono : Monotone fun n : ℕ ↦ RU ((n : ℝ) + 1)⁻¹ y := by
    intro m n hmn
    dsimp only
    rw [← hident _ (hpos m) y hy, ← hident _ (hpos n) y hy]
    refine IsConservative.killedResolvent_antitone P hP U hU (fun _ ↦ 1) y ?_
    exact inv_anti₀ (by positivity) (add_le_add (Nat.cast_le.mpr hmn) le_rfl)
  have hseq : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall fun n ↦ hpos n)
    have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [one_div] using h
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono) ((hw y hy).comp hseq)

/-- **The expected exit time from an identified Dirichlet resolvent.**  If the killed resolvent of
one agrees on `U` with a consumer-supplied family `RU` at every positive shift, and `RU` has the
pointwise limit `w` along the shifts `1 / (n + 1)`, then the expected exit time is `w`. -/
theorem IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq (U : Set alpha) (hU : IsOpen U)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hlim : ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y)
    {x : alpha} (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) = w x := by
  rw [IsConservative.lintegral_exitTime_eq_killedResolvent_zero P hP U hU x,
    IsConservative.killedResolvent_zero_eq_iSup P hP U hU measurable_const x, ← hlim x hx]
  refine iSup_congr fun n ↦ ?_
  exact hident _ (by positivity) x hx

/-- The upper half of the identification: a uniform upper bound on the limit bounds the expected
exit time. -/
theorem IsConservative.lintegral_exitTime_le_of_killedResolvent_eq (U : Set alpha) (hU : IsOpen U)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hlim : ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y)
    (M : ℝ≥0∞) (hupper : ∀ y ∈ U, w y ≤ M) {x : alpha} (hx : x ∈ U) :
    ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) ≤ M := by
  rw [IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq P hP RU w U hU hident hlim hx]
  exact hupper x hx

/-- The lower half of the identification: a uniform lower bound on the limit over a subset bounds
the expected exit time from below there. -/
theorem IsConservative.le_lintegral_exitTime_of_killedResolvent_eq (U : Set alpha) (hU : IsOpen U)
    (hident : ∀ lam : ℝ, 0 < lam → ∀ y ∈ U,
      IsConservative.killedResolvent P hP U hU lam (fun _ ↦ 1) y = RU lam y)
    (hlim : ∀ y ∈ U, ⨆ n : ℕ, RU ((n : ℝ) + 1)⁻¹ y = w y)
    (W : Set alpha) (hWU : W ⊆ U) (c : ℝ≥0∞) (hlower : ∀ y ∈ W, c ≤ w y)
    {x : alpha} (hx : x ∈ W) :
    c ≤ ∫⁻ omega, ContinuousPath.exitTime U omega ∂(IsConservative.continuousProcess P hP x) := by
  rw [IsConservative.lintegral_exitTime_eq_of_killedResolvent_eq P hP RU w U hU hident hlim
    (hWU hx)]
  exact hlower x hx

end

end MarkovProcess.SubMarkovKernelSemigroup

end PortComputability
