/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsDomain
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.OneVariable
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LocallyUniform

/-!
# Local estimates for Hartogs–Laurent series

Compact circles inside a Hartogs set give uniform bounds for nearby fibers. Two such circles
bound the positive and negative Laurent terms by geometric series. At the zero section the
negative coefficients vanish. These estimates upgrade a pointwise fiber expansion to locally
uniform convergence.

## Main results

`IsHartogs.exists_circle_bound` is a uniform bound on nearby fibers from a compact circle in a
Hartogs set. `hasSumLocallyUniformlyOn_hartogsLaurent` upgrades a pointwise fiber expansion to
locally uniform convergence on the Hartogs set.
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  {U : Set (E × ℂ)}

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Each fiber point of an open Hartogs set has a larger positive radius in the same fiber. -/
theorem IsHartogs.exists_larger_radius (hH : IsHartogs U) (hU : IsOpen U)
    {p : E × ℂ} (hp : p ∈ U) : ∃ R : ℝ, ‖p.2‖ < R ∧ (p.1, (R : ℂ)) ∈ U := by
  have hreal : (p.1, (‖p.2‖ : ℂ)) ∈ U := hH hp (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hreal
  refine ⟨‖p.2‖ + ε / 2, by linarith, hball ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨by simpa using hε, ?_⟩
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
  simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos (half_pos hε)]
  exact half_lt_self hε

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- A nonzero fiber point has a smaller positive radius in the same open Hartogs fiber. -/
theorem IsHartogs.exists_smaller_radius (hH : IsHartogs U) (hU : IsOpen U)
    {p : E × ℂ} (hp : p ∈ U) (hp0 : p.2 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < ‖p.2‖ ∧ (p.1, (r : ℂ)) ∈ U := by
  have hreal : (p.1, (‖p.2‖ : ℂ)) ∈ U := hH hp (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hreal
  let t := min ε ‖p.2‖ / 2
  have ht : 0 < t := half_pos (lt_min hε (norm_pos_iff.mpr hp0))
  have htε : t < ε := (half_lt_self (lt_min hε (norm_pos_iff.mpr hp0))).trans_le (min_le_left _ _)
  have htn : t < ‖p.2‖ :=
    (half_lt_self (lt_min hε (norm_pos_iff.mpr hp0))).trans_le (min_le_right _ _)
  refine ⟨‖p.2‖ - t, sub_pos.mpr htn, by linarith, hball ?_⟩
  rw [mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨by simpa using hε, ?_⟩
  rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
  simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg, abs_of_pos ht] using htε

omit [NormedSpace ℂ F] [CompleteSpace F] in
/-- A compact fiber circle has a common bound for the function on all nearby fibers. -/
theorem IsHartogs.exists_circle_bound (hH : IsHartogs U) (hU : IsOpen U)
    {f : E × ℂ → F} (hf : ContinuousOn f U) {z : E} {r : ℝ} (hr : 0 < r)
    (hz : (z, (r : ℂ)) ∈ U) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ y ∈ ball z δ, ∀ w ∈ sphere (0 : ℂ) r,
      (y, w) ∈ U ∧ ‖f (y, w)‖ ≤ M := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hnear : ∀ᶠ y in 𝓝 z, ∀ w ∈ sphere (0 : ℂ) r, (y, w) ∈ U := by
    apply (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually
    intro w hw
    exact hU.eventually_mem (hH hz (by
      rw [mem_sphere_zero_iff_norm.mp hw, Complex.norm_of_nonneg hr.le]))
  obtain ⟨δ, hδ, hδsub⟩ := nhds_basis_closedBall.mem_iff.mp hnear
  let K := closedBall z δ ×ˢ sphere (0 : ℂ) r
  have hKU : K ⊆ U := fun p hp => hδsub hp.1 p.2 hp.2
  obtain ⟨M, hM⟩ := ((isCompact_closedBall z δ).prod (isCompact_sphere (0 : ℂ) r)).bddAbove_image
    (hf.mono hKU).norm
  exact ⟨δ, max M 0, hδ, le_max_right _ _, fun y hy w hw =>
    ⟨hδsub (ball_subset_closedBall hy) w hw,
      (hM (mem_image_of_mem _ ⟨ball_subset_closedBall hy, hw⟩)).trans (le_max_left _ _)⟩⟩

omit [NormedSpace ℂ F] in
/-- Two geometric majorants, one for each half of the integers, give uniform convergence. -/
private theorem hasSumUniformlyOn_of_geometric_int_bounds {X : Type*} {N : Set X}
    {u : ℤ → X → F} {f : X → F} {M₁ M₂ q₁ q₂ : ℝ}
    (hq₁ : 0 ≤ q₁) (hq₁1 : q₁ < 1) (hq₂ : 0 ≤ q₂) (hq₂1 : q₂ < 1)
    (hsum : ∀ x ∈ N, HasSum (fun k => u k x) (f x))
    (hpos : ∀ n : ℕ, ∀ x ∈ N, ‖u n x‖ ≤ M₁ * q₁ ^ n)
    (hneg : ∀ n : ℕ, ∀ x ∈ N, ‖u (Int.negSucc n) x‖ ≤ M₂ * q₂ ^ (n + 1)) :
    HasSumUniformlyOn u f N := by
  have hs₁ := (summable_geometric_of_lt_one hq₁ hq₁1).mul_left M₁
  have hs₂ : Summable (fun n : ℕ => M₂ * q₂ ^ (n + 1)) := by
    simpa only [pow_succ, mul_assoc] using
      ((summable_geometric_of_lt_one hq₂ hq₂1).mul_left M₂).mul_right q₂
  have hbound (k : ℤ) (x : X) (hx : x ∈ N) :
      ‖u k x‖ ≤ Int.rec (fun n => M₁ * q₁ ^ n) (fun n => M₂ * q₂ ^ (n + 1)) k := by
    cases k with
    | ofNat n => exact hpos n x hx
    | negSucc n => exact hneg n x hx
  apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
  exact (tendstoUniformlyOn_tsum (hs₁.int_rec hs₂) hbound).congr_right
    (fun x hx => (hsum x hx).tsum_eq)

variable {f : E × ℂ → F} {a : ℤ → E → F}

/-- Near the zero section the positive terms have a common geometric bound and all negative terms
vanish. -/
private theorem exists_uniform_laurent_neighborhood_zero (hH : IsHartogs U) (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (hcoeff : ∀ (z : E) (r : ℝ), 0 < r → (z, (r : ℂ)) ∈ U →
      ∀ k, a k z = circleLaurentCoeff (fun w => f (z, w)) r k)
    (hzero : ∀ z, (z, 0) ∈ U → ∀ k : ℤ, k < 0 → a k z = 0)
    (hsum : ∀ p ∈ U, HasSum (fun k : ℤ => p.2 ^ k • a k p.1) (f p))
    {z : E} (hz : (z, (0 : ℂ)) ∈ U) :
    ∃ N ∈ 𝓝[U] (z, (0 : ℂ)), HasSumUniformlyOn (fun k p => p.2 ^ k • a k p.1) f N := by
  obtain ⟨R, hR', hzR⟩ := hH.exists_larger_radius hU hz
  have hR : 0 < R := by simpa using hR'
  obtain ⟨δ, M, hδ, _, hcircle⟩ := hH.exists_circle_bound hU hf hR hzR
  have hsection : Continuous (fun y : E => (y, (0 : ℂ))) :=
    continuous_id.prodMk continuous_const
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp ((hU.preimage hsection).mem_nhds hz)
  let N := (ball z (min δ ε) ×ˢ ball (0 : ℂ) (R / 2)) ∩ U
  have hN : N ∈ 𝓝[U] (z, (0 : ℂ)) := mem_nhdsWithin_of_mem_nhds
    (((isOpen_ball.prod isOpen_ball).inter hU).mem_nhds
      ⟨⟨mem_ball_self (lt_min hδ hε), mem_ball_self (half_pos hR)⟩, hz⟩)
  refine ⟨N, hN, ?_⟩
  apply hasSumUniformlyOn_of_geometric_int_bounds
    (M₁ := M) (q₁ := (R / 2) / R) (M₂ := 0) (q₂ := 0)
    (by positivity) ((div_lt_one hR).mpr (half_lt_self hR)) le_rfl zero_lt_one
    (fun p hp => hsum p hp.2)
  · intro n p hp
    have hc := hcircle p.1 ((ball_subset_ball (min_le_left δ ε)) hp.1.1)
    have hpr : (p.1, (R : ℂ)) ∈ U := (hc (R : ℂ) (by simp [hR.le])).1
    rw [hcoeff p.1 R hR hpr]
    exact norm_circleLaurentTerm_nat_le hR (fun w hw => (hc w hw).2)
      (mem_ball_zero_iff.mp hp.1.2).le n
  · intro n p hp
    have hp0 := hεsub ((ball_subset_ball (min_le_right δ ε)) hp.1.1)
    simp [hzero p.1 hp0 (Int.negSucc n) (by omega)]

/-- Away from zero, circles on either side of the fiber modulus give geometric majorants for both
halves of the Laurent series. -/
private theorem exists_uniform_laurent_neighborhood_ne_zero (hH : IsHartogs U) (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (hcoeff : ∀ (z : E) (r : ℝ), 0 < r → (z, (r : ℂ)) ∈ U →
      ∀ k, a k z = circleLaurentCoeff (fun w => f (z, w)) r k)
    (hsum : ∀ p ∈ U, HasSum (fun k : ℤ => p.2 ^ k • a k p.1) (f p))
    {p : E × ℂ} (hp : p ∈ U) (hp0 : p.2 ≠ 0) :
    ∃ N ∈ 𝓝[U] p, HasSumUniformlyOn (fun k q => q.2 ^ k • a k q.1) f N := by
  obtain ⟨R, hpR, hzR⟩ := hH.exists_larger_radius hU hp
  obtain ⟨r, hr, hrp, hzr⟩ := hH.exists_smaller_radius hU hp hp0
  have hR : 0 < R := (norm_nonneg _).trans_lt hpR
  obtain ⟨δ₁, M₁, hδ₁, _, hc₁⟩ := hH.exists_circle_bound hU hf hR hzR
  obtain ⟨δ₂, M₂, hδ₂, _, hc₂⟩ := hH.exists_circle_bound hU hf hr hzr
  let t := (r + ‖p.2‖) / 2
  let T := (‖p.2‖ + R) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have hrt : r < t := by dsimp [t]; linarith
  have htp : t < ‖p.2‖ := by dsimp [t]; linarith
  have hpT : ‖p.2‖ < T := by dsimp [T]; linarith
  have hTR : T < R := by dsimp [T]; linarith
  let V : Set ℂ := {w | t < ‖w‖ ∧ ‖w‖ < T}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  let N := (ball p.1 (min δ₁ δ₂) ×ˢ V) ∩ U
  refine ⟨N, mem_nhdsWithin_of_mem_nhds
    (((isOpen_ball.prod hV).inter hU).mem_nhds
      ⟨⟨mem_ball_self (lt_min hδ₁ hδ₂), htp, hpT⟩, hp⟩), ?_⟩
  apply hasSumUniformlyOn_of_geometric_int_bounds
    (M₁ := M₁) (q₁ := T / R) (M₂ := M₂) (q₂ := r / t)
    (by dsimp [T]; positivity) ((div_lt_one hR).mpr hTR)
    (by positivity) ((div_lt_one ht).mpr hrt) (fun q hq => hsum q hq.2)
  · intro n q hq
    have hc := hc₁ q.1 ((ball_subset_ball (min_le_left δ₁ δ₂)) hq.1.1)
    have hqR : (q.1, (R : ℂ)) ∈ U := (hc (R : ℂ) (by simp [hR.le])).1
    rw [hcoeff q.1 R hR hqR]
    exact norm_circleLaurentTerm_nat_le hR (fun w hw => (hc w hw).2) hq.1.2.2.le n
  · intro n q hq
    have hc := hc₂ q.1 ((ball_subset_ball (min_le_right δ₁ δ₂)) hq.1.1)
    have hqr : (q.1, (r : ℂ)) ∈ U := (hc (r : ℂ) (by simp [hr.le])).1
    rw [hcoeff q.1 r hr hqr]
    exact norm_circleLaurentTerm_negSucc_le hr ht (fun w hw => (hc w hw).2) hq.1.2.1.le n

/-- A pointwise Hartogs–Laurent expansion with circle coefficients converges locally uniformly. This
estimate is independent of Laurent expansion existence. -/
theorem hasSumLocallyUniformlyOn_hartogsLaurent (hH : IsHartogs U) (hU : IsOpen U)
    (hf : ContinuousOn f U)
    (hcoeff : ∀ (z : E) (r : ℝ), 0 < r → (z, (r : ℂ)) ∈ U →
      ∀ k, a k z = circleLaurentCoeff (fun w => f (z, w)) r k)
    (hzero : ∀ z, (z, 0) ∈ U → ∀ k : ℤ, k < 0 → a k z = 0)
    (hsum : ∀ p ∈ U, HasSum (fun k : ℤ => p.2 ^ k • a k p.1) (f p)) :
    HasSumLocallyUniformlyOn (fun k p => p.2 ^ k • a k p.1) f U := by
  apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
  rintro ⟨z, w⟩ hp
  by_cases hp0 : w = 0
  · subst w
    exact exists_uniform_laurent_neighborhood_zero hH hU hf hcoeff hzero hsum hp
  · exact exists_uniform_laurent_neighborhood_ne_zero hH hU hf hcoeff hsum hp hp0

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
