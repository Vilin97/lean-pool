/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.OrbitContinuity
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.OrbitProductRule
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Resolvent

/-!
# Comparing two semigroups through their resolvents

Two strongly continuous contraction semigroups `S` and `S'` on the same Banach space have, in
general, unrelated generator domains, so the naive Duhamel comparison of their orbits is not
available.  Inserting one resolvent of each semigroup repairs this: the curve

  `y ↦ S y (R_μ (S' (t − y) (R'_μ z)))`,

where `R_μ` and `R'_μ` are the resolvents of `S` and of `S'` at a positive shift `μ`, takes values
in the generator domain of `S` at every time, is differentiable because `R'_μ z` lies in the
generator domain of `S'`, and its derivative telescopes to the difference of the two resolvents:

  `S t (R_μ (R'_μ z)) − R_μ (S' t (R'_μ z)) = ∫₀ᵗ S y ((R_μ − R'_μ) (S' (t − y) z)) dy.`

Consequently the left-hand side is bounded by `t` times the largest value of `‖(R_μ − R'_μ) v‖`
over the orbit `{S' u z : 0 ≤ u ≤ t}`, which is a compact set.  This is the mechanism behind the
Trotter--Kato theorem in `Semigroup/TrotterKato.lean`.

Main results: `operator_resolvent_sub_resolvent_operator_eq_integral`,
`norm_operator_resolvent_sub_resolvent_operator_le`.

Both semigroups are read at the same shift `μ`; nothing is asserted when the two resolvents are
taken at different shifts, and no relation between the two generators is assumed.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The derivative of the comparison curve `u ↦ S u (R_μ (S' (t − u) (R'_μ z)))` at an interior
time is `S y ((R_μ − R'_μ) (S' (t − y) z))`: the generator of `S` acting on the resolvent value
and the derivative of the inner orbit cancel except for the difference of the resolvents. -/
private theorem hasDerivWithinAt_comparison
    (S S' : StronglyContinuousContractionSemigroup E) (μ : PositiveShift) (t : ℝ) (z : E)
    {y : ℝ} (hy0 : 0 ≤ y) (hyt : y < t) :
    HasDerivWithinAt
      (fun u : ℝ ↦ S (Real.toNNReal u)
        (S.resolvent μ (S' (Real.toNNReal (t - u)) (S'.resolvent μ z))))
      (S (Real.toNNReal y)
        (S.resolvent μ (S' (Real.toNNReal (t - y)) z) -
          S'.resolvent μ (S' (Real.toNNReal (t - y)) z)))
      (Set.Ioi y) y := by
  have hwmem : S'.resolvent μ z ∈ S'.generatorDomain := S'.resolvent_mem_generatorDomain μ z
  have hmem : S.resolvent μ (S' (Real.toNNReal (t - y)) (S'.resolvent μ z)) ∈
      S.generatorDomain := S.resolvent_mem_generatorDomain μ _
  have hty : (0 : ℝ) < t - y := sub_pos.mpr hyt
  have h1 : HasDerivAt (fun u : ℝ ↦ S' (Real.toNNReal u) (S'.resolvent μ z))
      (S' (Real.toNNReal (t - y)) (S'.generator ⟨S'.resolvent μ z, hwmem⟩)) (t - y) :=
    S'.hasDerivAt_operator_toNNReal ⟨S'.resolvent μ z, hwmem⟩ hty
  have h2 : HasDerivAt (fun u : ℝ ↦ t - u) (-1) y := by
    simpa using! (hasDerivAt_const y t).sub (hasDerivAt_id y)
  have h3 := h1.scomp (𝕜 := ℝ) y h2
  have hd : HasDerivWithinAt
      (fun u : ℝ ↦ S.resolvent μ (S' (Real.toNNReal (t - u)) (S'.resolvent μ z)))
      (S.resolvent μ ((-1 : ℝ) •
        S' (Real.toNNReal (t - y)) (S'.generator ⟨S'.resolvent μ z, hwmem⟩)))
      (Set.Ioi y) y :=
    ((S.resolvent μ).hasFDerivAt.comp_hasDerivAt y h3).hasDerivWithinAt
  refine (S.hasDerivWithinAt_operator_apply hy0 hmem hd).congr_deriv ?_
  have hgen1 : S.generator ⟨S.resolvent μ (S' (Real.toNNReal (t - y)) (S'.resolvent μ z)),
      hmem⟩ =
      (μ : ℝ) • S.resolvent μ (S' (Real.toNNReal (t - y)) (S'.resolvent μ z)) -
        S' (Real.toNNReal (t - y)) (S'.resolvent μ z) :=
    S.generator_eq_of_resolvent_eq μ hmem rfl
  have hgen2 : S'.generator ⟨S'.resolvent μ z, hwmem⟩ = (μ : ℝ) • S'.resolvent μ z - z :=
    S'.generator_eq_of_resolvent_eq μ hwmem rfl
  have hcomm : S' (Real.toNNReal (t - y)) (S'.resolvent μ z) =
      S'.resolvent μ (S' (Real.toNNReal (t - y)) z) :=
    S'.operator_resolvent μ _ z
  congr 1
  rw [hgen1, hgen2]
  simp only [map_sub, map_smul, hcomm]
  module

/-- **The resolvent comparison identity.**  For two strongly continuous contraction semigroups
`S` and `S'` with resolvents `R_μ` and `R'_μ` at a common positive shift,
`S t (R_μ (R'_μ z)) − R_μ (S' t (R'_μ z)) = ∫₀ᵗ S y ((R_μ − R'_μ) (S' (t − y) z)) dy`. -/
theorem operator_resolvent_sub_resolvent_operator_eq_integral
    (S S' : StronglyContinuousContractionSemigroup E) (μ : PositiveShift) (t : NNReal) (z : E) :
    S t (S.resolvent μ (S'.resolvent μ z)) - S.resolvent μ (S' t (S'.resolvent μ z)) =
      ∫ y in (0 : ℝ)..(t : ℝ), S (Real.toNNReal y)
        (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z) -
          S'.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z)) := by
  have hcurve : Continuous fun u : ℝ ↦ S (Real.toNNReal u)
      (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - u)) (S'.resolvent μ z))) := by
    refine S.continuous_operator_apply continuous_real_toNNReal ?_
    exact (S.resolvent μ).continuous.comp
      ((S'.continuous_operator_toNNReal (S'.resolvent μ z)).comp
        (continuous_const.sub continuous_id))
  have hderiv : Continuous fun u : ℝ ↦ S (Real.toNNReal u)
      (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - u)) z) -
        S'.resolvent μ (S' (Real.toNNReal ((t : ℝ) - u)) z)) := by
    refine S.continuous_operator_apply continuous_real_toNNReal ?_
    have h : Continuous fun u : ℝ ↦ S' (Real.toNNReal ((t : ℝ) - u)) z :=
      (S'.continuous_operator_toNNReal z).comp (continuous_const.sub continuous_id)
    exact ((S.resolvent μ).continuous.comp h).sub ((S'.resolvent μ).continuous.comp h)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg
    hcurve.continuousOn
    (fun y hy ↦ hasDerivWithinAt_comparison S S' μ (t : ℝ) z hy.1.le hy.2)
    (hderiv.intervalIntegrable 0 (t : ℝ))
  rw [hFTC]
  simp only [sub_self, sub_zero, Real.toNNReal_zero, Real.toNNReal_coe, zero_apply]

/-- **The resolvent comparison estimate.**  If the two resolvents differ by at most `ε` along the
orbit `{S' u z : 0 ≤ u ≤ t}`, then the comparison identity is bounded by `t ε`. -/
theorem norm_operator_resolvent_sub_resolvent_operator_le
    (S S' : StronglyContinuousContractionSemigroup E) (μ : PositiveShift) (t : NNReal) (z : E)
    {ε : ℝ} (h : ∀ u ∈ Set.Icc (0 : ℝ) (t : ℝ),
      ‖S.resolvent μ (S' (Real.toNNReal u) z) - S'.resolvent μ (S' (Real.toNNReal u) z)‖ ≤ ε) :
    ‖S t (S.resolvent μ (S'.resolvent μ z)) - S.resolvent μ (S' t (S'.resolvent μ z))‖ ≤
      (t : ℝ) * ε := by
  rw [operator_resolvent_sub_resolvent_operator_eq_integral]
  have hbound : ∀ y ∈ Set.uIoc (0 : ℝ) (t : ℝ),
      ‖S (Real.toNNReal y) (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z) -
        S'.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z))‖ ≤ ε := by
    intro y hy
    rw [Set.uIoc_of_le t.coe_nonneg] at hy
    exact le_trans (S.norm_apply_le _ _)
      (h _ ⟨by linarith [hy.2], by linarith [hy.1]⟩)
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) (le_of_eq ?_)
  rw [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm]

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
