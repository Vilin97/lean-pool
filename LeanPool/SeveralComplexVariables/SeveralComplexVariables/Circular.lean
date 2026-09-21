/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Reinhardt

/-!
# Circular sets and balanced geometry

Circular symmetry rotates all coordinates by the same scalar. This is weaker than Reinhardt
symmetry. Openness, connectedness and nonemptiness remain separate properties. Balanced sets and
their hulls use Mathlib's `Balanced` and `balancedHull`. Reference:
[Scheidemann][Scheidemann2005] (2005), Section 2.1 and Corollary 3.3.3.

## Main definitions

* `IsCircular`: Invariance under one common complex rotation, about the origin.

## Main results

* `isCircular_of_balanced`: Balanced sets are circular, including the empty set.
* `isCircular_balancedHull`: Mathlib's balanced hull is circular.
* `isPathConnected_balancedHull`: A nonempty balanced hull is path connected, independently of the
  original set's connectedness.
* `IsReinhardt.isCircular`: Independent coordinate rotations include common rotations.
* `IsCompleteReinhardt.balanced`: Complete Reinhardt sets are balanced for complex scalar
  multiplication.

## References

* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Set Metric

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {U V : Set E}

/-- Invariance under one common complex rotation, about the origin. -/
@[expose] def IsCircular (U : Set E) : Prop :=
  ∀ ⦃z⦄, z ∈ U → ∀ ⦃c : ℂ⦄, ‖c‖ = 1 → c • z ∈ U

/-- Multiplication by a complex scalar of norm one preserves a circular set. -/
theorem IsCircular.smul_mem (hU : IsCircular U) {z : E} (hz : z ∈ U)
    {c : ℂ} (hc : ‖c‖ = 1) : c • z ∈ U := hU hz hc

/-- The empty set is circular. -/
theorem isCircular_empty : IsCircular (∅ : Set E) := fun _ h => h.elim

/-- The whole space is circular. -/
theorem isCircular_univ : IsCircular (univ : Set E) := fun _ _ _ _ => mem_univ _

/-- Intersections preserve circular symmetry. -/
theorem IsCircular.inter (hU : IsCircular U) (hV : IsCircular V) : IsCircular (U ∩ V) :=
  fun _ hz _ hc => ⟨hU hz.1 hc, hV hz.2 hc⟩

/-- Unions preserve circular symmetry. -/
theorem IsCircular.union (hU : IsCircular U) (hV : IsCircular V) : IsCircular (U ∪ V) :=
  fun _ hz _ hc => hz.elim (fun h => Or.inl (hU h hc)) (fun h => Or.inr (hV h hc))

/-- Balanced sets are circular, including the empty set. -/
theorem isCircular_of_balanced (hU : Balanced ℂ U) : IsCircular U :=
  fun _ hz _ hc => (balanced_iff_smul_mem.mp hU) hc.le hz

/-- Mathlib's balanced hull is circular. -/
theorem isCircular_balancedHull (U : Set E) : IsCircular (balancedHull ℂ U) :=
  isCircular_of_balanced (balancedHull.balanced U)

/-- A nonempty balanced hull is path connected, independently of the original set's connectedness.
This follows by contraction along the real radial segments. -/
theorem isPathConnected_balancedHull (hne : U.Nonempty) : IsPathConnected (balancedHull ℂ U) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  have hB := balancedHull.balanced (𝕜 := ℂ) U
  have hs : StarConvex ℝ (0 : E) (balancedHull ℂ U) := by
    intro z hz a b ha hb hab
    simp only [smul_zero, zero_add]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    apply (balanced_iff_smul_mem.mp hB) _ hz
    simpa [abs_of_nonneg hb] using (show b ≤ 1 by linarith)
  exact hs.isPathConnected (hB.zero_mem (hne.mono (subset_balancedHull ℂ)))

/-- Linear inverse images preserve circular symmetry. -/
theorem IsCircular.preimage (L : E →L[ℂ] F) {V : Set F} (hV : IsCircular V) :
    IsCircular (L ⁻¹' V) := by
  intro z hz c hc
  change L (c • z) ∈ V
  rw [map_smul]
  exact hV hz hc

/-- Balls about zero are circular for any complex norm, without a coordinate assumption. -/
theorem isCircular_ball (r : ℝ) : IsCircular (ball (0 : E) r) := by
  intro z hz c hc
  simpa only [mem_ball, dist_zero_right, norm_smul, hc, one_mul] using hz

/-- Independent coordinate rotations include common rotations. -/
theorem IsReinhardt.isCircular {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (hU : IsReinhardt U) : IsCircular U := by
  intro z hz c hc
  exact hU hz (fun i => by simp [hc])

/-- Complete Reinhardt sets are balanced for complex scalar multiplication. -/
theorem IsCompleteReinhardt.balanced {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (hU : IsCompleteReinhardt U) : Balanced ℂ U := by
  rw [balanced_iff_smul_mem]
  intro c hc z hz
  apply hU hz
  intro i
  simpa only [Pi.smul_apply, norm_smul, one_mul] using
    mul_le_mul_of_nonneg_right hc (norm_nonneg (z i))

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
