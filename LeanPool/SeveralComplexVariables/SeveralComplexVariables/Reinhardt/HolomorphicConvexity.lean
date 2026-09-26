/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HolomorphicConvexity.Hull
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Polydisc
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt.MonomialSeparation

/-!
# Holomorphic convexity of complete Reinhardt domains

An exterior point is separated from each compact subset by a monomial. The entire holomorphic
hull of the compact set therefore stays in the domain. Its compactness implies compactness of
the relative holomorphic hull.

## Main results

`exists_monomial_separator_of_isCompact` separates an exterior point from a compact subset by a
monomial. `isHolomorphicallyConvex_of_completeReinhardt` is holomorphic convexity of an open
complete logarithmically convex Reinhardt domain.
-/

public noncomputable section

open Set
open scoped Topology NNReal

namespace SeveralComplexVariables

variable {ι : Type*} [Fintype ι]

/-- A monomial separates a compact subset of an open complete logarithmically convex Reinhardt set
from any exterior point. -/
theorem exists_monomial_separator_of_isCompact {U K : Set (ι → ℂ)}
    (ho : IsOpen U) (hc : IsCompleteReinhardt U) (hl : IsLogarithmicallyConvex U)
    (hK : IsCompact K) (hKU : K ⊆ U) {z : ι → ℂ} (hz : z ∉ U) :
    ∃ (m : ι → ℕ) (M : ℝ), (∀ w ∈ K, ‖∏ i, w i ^ m i‖ ≤ M) ∧
      M < ‖∏ i, z i ^ m i‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, 0, by simp, by simp⟩
  let R := {r : ι → ℝ≥0 | (fun i => (r i : ℂ)) ∈ U ∧ ∀ i, 0 < r i}
  let P (r : R) := polydisc (0 : ι → ℂ) (fun i => (r.val i : ℝ))
  have hcover : K ⊆ ⋃ r : R, P r := by
    intro w hw
    obtain ⟨r, hrU, hr⟩ := hc.isReinhardt.exists_strict_modulus_majorant ho (hKU hw)
    have hrpos (i) : 0 < r i := (show (0 : ℝ≥0) ≤ ‖w i‖₊ from zero_le).trans_lt (hr i)
    apply mem_iUnion.mpr
    refine ⟨⟨r, hrU, hrpos⟩, ?_⟩
    apply mem_polydisc.mpr
    intro i
    simpa only [dist_zero_right, Pi.zero_apply] using (show ‖w i‖ < (r i : ℝ) from hr i)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover P (fun r => isOpen_polydisc _ _) hcover
  have hsne : s.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    obtain ⟨r, hr, _⟩ := mem_iUnion₂.mp (hs hw)
    exact ⟨r, hr⟩
  let : Nonempty s := hsne.to_subtype
  let r (j : s) (i : ι) : ℝ := j.val.val i
  have hr (j : s) (i : ι) : 0 < r j i := j.val.property.2 i
  obtain ⟨m, hm⟩ := exists_monomial_separator_of_finite_radii ho hc hl hr
    (fun j => j.val.property.1) hz
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image (Finset.univ : Finset s)
    (fun j => ∏ i, r j i ^ m i) Finset.univ_nonempty
  refine ⟨m, ∏ i, r j i ^ m i, ?_, ?_⟩
  · intro w hw
    obtain ⟨q, hq, hwq⟩ := mem_iUnion₂.mp (hs hw)
    rw [norm_prod]
    simp only [norm_pow]
    apply le_trans _ (hj ⟨q, hq⟩ (Finset.mem_univ _))
    apply Finset.prod_le_prod₀ (fun i _ => pow_nonneg (norm_nonneg _) _)
    intro i _
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [Pi.zero_apply, dist_zero_right] using
      (mem_polydisc.mp hwq i).le
  · simpa only [norm_prod, norm_pow] using hm j

/-- Open complete logarithmically convex Reinhardt sets are holomorphically convex. This includes
unbounded sets, the empty set, and empty coordinate types. -/
theorem isHolomorphicallyConvex_of_completeReinhardt {U : Set (ι → ℂ)}
    (ho : IsOpen U) (hc : IsCompleteReinhardt U) (hl : IsLogarithmicallyConvex U) :
    IsHolomorphicallyConvex U := by
  intro K hK hKU
  have hC : IsCompact (holomorphicHull univ K) :=
    isHolomorphicallyConvex_univ K hK (subset_univ _)
  have hCU : holomorphicHull univ K ⊆ U := by
    intro z hz
    by_contra hn
    obtain ⟨m, M, hM, hMz⟩ := exists_monomial_separator_of_isCompact ho hc hl hK hKU hn
    have hf : AnalyticOnNhd ℂ (fun w : ι → ℂ => ∏ i, w i ^ m i) univ := by
      intro w _
      apply Finset.analyticAt_fun_prod
      intro i _
      exact ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt w).pow (m i)
    exact (hz.2 _ hf M hM).not_gt hMz
  exact isCompact_holomorphicHull_of_subset_compact hC hCU
    (holomorphicHull_mono_ambient (subset_univ _))

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
