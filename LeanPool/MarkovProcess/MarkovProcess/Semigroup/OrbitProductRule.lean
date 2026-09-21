/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Generator

/-!
# The product rule for a semigroup acting along a curve

Let `S` be a strongly continuous contraction semigroup with generator `L` and let `v` be a curve
in the Banach space which is right differentiable at a time `s ≥ 0` and whose value `v s` lies in
the generator domain.  Then the evolved curve `y ↦ S y (v y)` is right differentiable at `s` with

  `d⁺/dy [ S y (v y) ] = S s (L (v s) + v' s)`.

The proof splits the increment as `S y (v y − v s) + S s (S (y − s) (v s) − v s)`.  The first
summand is handled by contractivity and strong continuity, the second is the difference quotient
that defines the generator; no differentiability of `y ↦ S y` in the operator norm is used, and
only the value of `v` at the single time `s` is required to lie in the domain.

Main results: `hasDerivWithinAt_operator_apply`.

Times are read from the real line at `Real.toNNReal`, as elsewhere in the library.  Nothing is
asserted about the two-sided derivative, which for a general curve fails at `s = 0`.
-/

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

/-- **The product rule for the evolution of a curve.**  If the curve `v` has right derivative
`v'` at the nonnegative time `s` and `v s` lies in the generator domain, then `y ↦ S y (v y)` has
right derivative `S s (L (v s) + v')` at `s`. -/
theorem hasDerivWithinAt_operator_apply {v : ℝ → E} {v' : E} {s : ℝ} (hs : 0 ≤ s)
    (hmem : v s ∈ S.generatorDomain) (hv : HasDerivWithinAt v v' (Set.Ioi s) s) :
    HasDerivWithinAt (fun y : ℝ ↦ S (Real.toNNReal y) (v y))
      (S (Real.toNNReal s) (S.generator ⟨v s, hmem⟩ + v')) (Set.Ioi s) s := by
  have hdiff : Set.Ioi s \ {s} = Set.Ioi s := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact fun hy ↦ ne_of_gt hy
  have hcoe : ((Real.toNNReal s : NNReal) : ℝ) = s := Real.coe_toNNReal s hs
  have hslope : Tendsto (slope v s) (𝓝[>] s) (𝓝 v') := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hv
    rwa [hdiff] at h
  have hA : Tendsto (fun y : ℝ ↦ S (Real.toNNReal y) (slope v s y)) (𝓝[>] s)
      (𝓝 (S (Real.toNNReal s) v')) := by
    refine tendsto_apply_of_opNorm_le_one (fun y : ℝ ↦ S (Real.toNNReal y))
      (S (Real.toNNReal s)) (slope v s) v' (fun y ↦ S.norm_operator_le_one _) ?_ hslope
    exact ((S.continuous_operator_toNNReal v').tendsto s).mono_left nhdsWithin_le_nhds
  have hsub : Tendsto (fun y : ℝ ↦ Real.toNNReal (y - s)) (𝓝[>] s) (𝓝[>] 0) := by
    have h := tendsto_toNNReal_sub (Real.toNNReal s)
    rwa [hcoe] at h
  have hB : Tendsto (fun y : ℝ ↦
      S (Real.toNNReal s) (S.differenceQuotient (v s) (Real.toNNReal (y - s)))) (𝓝[>] s)
      (𝓝 (S (Real.toNNReal s) (S.generator ⟨v s, hmem⟩))) :=
    ((S (Real.toNNReal s)).continuous.tendsto _).comp
      ((S.tendsto_generator ⟨v s, hmem⟩).comp hsub)
  have hlim : S (Real.toNNReal s) v' + S (Real.toNNReal s) (S.generator ⟨v s, hmem⟩) =
      S (Real.toNNReal s) (S.generator ⟨v s, hmem⟩ + v') := by
    rw [map_add]
    abel
  rw [hasDerivWithinAt_iff_tendsto_slope, hdiff, ← hlim]
  refine (hA.add hB).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hys : s < y := hy
  have hk : ((Real.toNNReal (y - s) : NNReal) : ℝ) = y - s :=
    Real.coe_toNNReal _ (sub_nonneg.mpr hys.le)
  have hsum : Real.toNNReal s + Real.toNNReal (y - s) = Real.toNNReal y := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, hk, hcoe, Real.coe_toNNReal y (hs.trans hys.le)]
    ring
  have hshift : S (Real.toNNReal s) (S (Real.toNNReal (y - s)) (v s)) =
      S (Real.toNNReal y) (v s) := by
    rw [← S.add_apply, hsum]
  show S (Real.toNNReal y) (slope v s y) +
      S (Real.toNNReal s) (S.differenceQuotient (v s) (Real.toNNReal (y - s))) =
    slope (fun y : ℝ ↦ S (Real.toNNReal y) (v y)) s y
  rw [slope_def_module, slope_def_module, S.differenceQuotient_apply, hk, map_smul, map_smul,
    map_sub, map_sub, hshift]
  module

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
