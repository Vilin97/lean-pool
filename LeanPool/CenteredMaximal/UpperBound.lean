/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.CenteredMaximal.Basic
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The upper bound `c_d ≤ 2ᵈ`

Let `E = {M f > α}`. Every `x ∈ E` is the centre of a cube `Q_x` with `α |Q_x| < ∫_{Q_x} |f|`;
these cubes have bounded radii. Mathlib's Vitali lemma with enlargement `τ > 1` selects a disjoint
subfamily such that every `Q_x` meets a selected `Q_b` with `r_x ≤ τ r_b`. Then the *centre*
`x` lies in the cube of radius `(1 + τ) r_b` about `b`; covering only the centres is what saves
the factor `3ᵈ` of the uncentred argument. Summing over the disjoint selected cubes gives
`α |E| ≤ (1 + τ)ᵈ ‖f‖₁`, and letting `τ → 1` gives `2ᵈ` (Tao, 245A Notes 5, Exercise 42, whose
hint notes that one needs an epsilon of room).
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace LeanPool.CenteredMaximal

variable {d : ℕ}

/-- In dimension `0` the space `Fin 0 → ℝ` is a single point of volume `1`, and `1` is a weak type
bound. This is the case `d = 0` of `isWeakTypeBound_two_pow`. -/
theorem isWeakTypeBound_zero_one : IsWeakTypeBound 0 1 := by
  intro f _ α
  rcases eq_empty_or_nonempty {x | α < maximalFunction f x} with hE | ⟨x, hx⟩
  · simp [hE]
  -- every cube in the one-point space has volume `1`, so `M f ≤ ‖f‖₁`
  have hM : maximalFunction f x ≤ ∫⁻ y, ‖f y‖ₑ := iSup₂_le fun r hr ↦ by
    simpa [volume_closedBall_eq x hr.le] using setLIntegral_le_lintegral _ _
  calc α * volume {x | α < maximalFunction f x} ≤ α * 1 :=
        mul_le_mul_right ((measure_mono (subset_univ _)).trans_eq (Measure.pi_empty_univ _)) α
    _ ≤ 1 * ∫⁻ y, ‖f y‖ₑ := by simpa using (hx.trans_le hM).le

/-- In positive dimension, a cube whose volume times `α ∈ (0, ∞)` stays below a finite `K` has
radius at most `max 1 (K / α)`. With `K = ‖f‖₁` this is the uniform bound on the radii of the
cubes in `mul_volume_le_of_one_lt`, which the Vitali covering lemma requires. -/
theorem radius_le_of_mul_volume_lt (hd : 0 < d) {α K : ℝ≥0∞} (hα : 0 < α) (hα' : α ≠ ∞) (hK : K ≠ ∞)
    {x : Fin d → ℝ} {r : ℝ} (hr : 0 < r) (h : α * volume (closedBall x r) < K) :
    r ≤ max 1 (K / α).toReal := by
  by_contra! hlt
  obtain ⟨h₁, h₂⟩ := max_lt_iff.1 hlt
  -- then `|Q| = (2r)ᵈ ≥ 2r > K / α`, so `α |Q| ≥ K`, contradicting `h`
  refine h.not_ge ?_
  rw [volume_closedBall_eq x hr.le, ← ENNReal.div_le_iff' hα.ne' hα',
    ENNReal.le_ofReal_iff_toReal_le (ENNReal.div_ne_top hK hα.ne') (by positivity)]
  linarith [le_self_pow₀ (by linarith : 1 ≤ 2 * r) hd.ne']

private theorem exists_mul_volume_lt_setLIntegral {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} {α : ℝ≥0∞}
    (h : α < maximalFunction f x) :
    ∃ r, 0 < r ∧ α * volume (closedBall x r) < ∫⁻ y in closedBall x r, ‖f y‖ₑ := by
  obtain ⟨r, hr, hlt⟩ := exists_lt_average_of_lt_maximalFunction h
  exact ⟨r, hr, ENNReal.mul_lt_of_lt_div (ENNReal.div_eq_inv_mul ▸ hlt)⟩

private theorem subset_biUnion_closedBall_one_add_mul {X : Type*} [PseudoMetricSpace X]
    {E u : Set X} {ρ : X → ℝ} {τ : ℝ}
    (h : ∀ a ∈ E, ∃ b ∈ u, (closedBall a (ρ a) ∩ closedBall b (ρ b)).Nonempty ∧ ρ a ≤ τ * ρ b) :
    E ⊆ ⋃ b ∈ u, closedBall b ((1 + τ) * ρ b) := fun a ha ↦
  let ⟨b, hbu, hab, hρ⟩ := h a ha
  mem_biUnion hbu <| (dist_le_add_of_nonempty_closedBall_inter_closedBall hab).trans (by linarith)

private theorem volume_biUnion_closedBall_mul_le {u : Set (Fin d → ℝ)} (hu : u.Countable)
    {ρ : (Fin d → ℝ) → ℝ} (hρ : ∀ b ∈ u, 0 ≤ ρ b) {c : ℝ} (hc : 0 ≤ c) :
    volume (⋃ b ∈ u, closedBall b (c * ρ b)) ≤ ENNReal.ofReal (c ^ d) *
      ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b)) := by
  rw [← ENNReal.tsum_mul_left]
  refine (measure_biUnion_le volume hu _).trans_eq (tsum_congr fun b ↦ ?_)
  rw [volume_closedBall_eq _ (mul_nonneg hc (hρ b b.2)), volume_closedBall_eq _ (hρ b b.2),
    ← ENNReal.ofReal_mul (by positivity), mul_left_comm, mul_pow]

private theorem mul_tsum_volume_le_lintegral {f : (Fin d → ℝ) → ℝ} {α : ℝ≥0∞} {u : Set (Fin d → ℝ)}
    (hu : u.Countable) {ρ : (Fin d → ℝ) → ℝ} (hdisj : u.PairwiseDisjoint fun b ↦ closedBall b (ρ b))
    (hρ : ∀ b ∈ u, α * volume (closedBall b (ρ b)) ≤ ∫⁻ y in closedBall b (ρ b), ‖f y‖ₑ) :
    α * ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b)) ≤ ∫⁻ x, ‖f x‖ₑ :=
  calc α * ∑' b : u, volume (closedBall (b : Fin d → ℝ) (ρ b))
      ≤ ∑' b : u, ∫⁻ y in closedBall (b : Fin d → ℝ) (ρ b), ‖f y‖ₑ :=
        ENNReal.tsum_mul_left.symm.trans_le (ENNReal.tsum_le_tsum fun b ↦ hρ b b.2)
    _ = ∫⁻ y in ⋃ b ∈ u, closedBall b (ρ b), ‖f y‖ₑ :=
        (lintegral_biUnion hu (fun _ _ ↦ measurableSet_closedBall) hdisj _).symm
    _ ≤ ∫⁻ x, ‖f x‖ₑ := setLIntegral_le_lintegral _ _

/-- Weak type bound with an epsilon of room: in positive dimension,
`α |{M f > α}| ≤ (1 + τ)ᵈ ‖f‖₁` for every `τ > 1`. Letting `τ → 1` gives the bound `2ᵈ` of
`isWeakTypeBound_two_pow`; the case `d = 0` is `isWeakTypeBound_zero_one`. -/
theorem mul_volume_le_of_one_lt (hd : 0 < d) {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) (α : ℝ≥0∞)
    {τ : ℝ} (hτ : 1 < τ) :
    α * volume {x | α < maximalFunction f x} ≤ ENNReal.ofReal ((1 + τ) ^ d) * ∫⁻ x, ‖f x‖ₑ := by
  rcases eq_zero_or_pos α with rfl | hα
  · simp
  rcases eq_or_ne α ∞ with rfl | hαt
  · simp
  set E := {x | α < maximalFunction f x}
  -- every `x ∈ E` is the centre of a cube `Q_x` of radius `ρ x` with `α |Q_x| < ∫_{Q_x} |f|`
  choose! ρ hρ₀ hρ using fun x (hx : x ∈ E) ↦ exists_mul_volume_lt_setLIntegral hx
  -- the radii are bounded, so Vitali selects disjoint cubes `Q_b`, `b ∈ u`, such that every `Q_x`
  -- meets some `Q_b` with `ρ x ≤ τ ρ b`
  obtain ⟨u, huE, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x ↦ closedBall x (ρ x)) E ρ τ hτ (fun x hx ↦ (hρ₀ x hx).le) _
    (fun x hx ↦ radius_le_of_mul_volume_lt hd hα hαt (hasFiniteIntegral_iff_enorm.1 hf.2).ne
      (hρ₀ x hx) ((hρ x hx).trans_le (setLIntegral_le_lintegral _ _)))
    fun x hx ↦ ⟨x, mem_closedBall_self (hρ₀ x hx).le⟩
  have hu : u.Countable := hdisj.countable_of_nonempty_interior fun x hx ↦
    ⟨x, interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self (hρ₀ x (huE hx)))⟩
  -- the centres of `E` lie in the `(1 + τ)`-enlarged `Q_b`, and the `Q_b` are disjoint
  grw [subset_biUnion_closedBall_one_add_mul hcov,
    volume_biUnion_closedBall_mul_le hu (fun b hb ↦ (hρ₀ b (huE hb)).le) (by linarith),
    mul_left_comm, mul_tsum_volume_le_lintegral hu hdisj fun b hb ↦ (hρ b (huE hb)).le]

/-- `2ᵈ` is a weak type bound in dimension `d`, so `weakTypeConstant d ≤ 2 ^ d` by
`weakTypeConstant_le`. Compare `mul_volume_le_of_one_lt`, which gives only the weaker bound
`(1 + τ)ᵈ` for each fixed `τ > 1`, and only in positive dimension. -/
theorem isWeakTypeBound_two_pow (d : ℕ) : IsWeakTypeBound d (2 ^ d) := by
  rcases d.eq_zero_or_pos with rfl | hd
  · simpa using isWeakTypeBound_zero_one
  intro f hf α
  -- let `τ → 1⁺` in the bounds `α |{M f > α}| ≤ (1 + τ)ᵈ ‖f‖₁` of `mul_volume_le_of_one_lt`
  refine ge_of_tendsto (x := 𝓝[>] (1 : ℝ)) (ENNReal.Tendsto.mul_const ?_ (.inr hf.2.ne))
    (eventually_nhdsWithin_of_forall fun _ ↦ mul_volume_le_of_one_lt hd hf α)
  -- the constants converge: `(1 + τ)ᵈ → (1 + 1)ᵈ = 2ᵈ`
  exact ((ENNReal.continuous_ofReal.comp (by fun_prop)).tendsto' 1 _
    (by norm_num [ENNReal.ofReal_pow])).mono_left nhdsWithin_le_nhds

end LeanPool.CenteredMaximal
