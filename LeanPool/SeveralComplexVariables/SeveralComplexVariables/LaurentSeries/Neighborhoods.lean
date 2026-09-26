/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Polydisc

/-!
# Circular product neighborhoods in Reinhardt sets

An open Reinhardt set contains a product of connected circular domains around each point,
including points on coordinate hyperplanes.

## Main results

`IsReinhardt.exists_circular_product_neighborhood` produces such a product neighborhood of any
point. `isConnected_complex_annulus` and `isConnected_norm_preimage_ball` record connectedness
of the circular factors, including degenerate annuli that meet a coordinate hyperplane.
-/

public noncomputable section

open Complex Set Metric
open scoped Topology

namespace SeveralComplexVariables

/-- An open annulus with nonnegative inner radius is connected. -/
theorem isConnected_complex_annulus {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    IsConnected {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
  have hc := (isConnected_Ioo hab).prod (isConnected_univ : IsConnected (univ : Set ℝ))
  have hcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) := by fun_prop
  have he : (fun p : ℝ × ℝ => (p.1 : ℂ) * exp (p.2 * I)) '' (Ioo a b ×ˢ univ) =
      {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b} := by
    ext z
    constructor
    · rintro ⟨⟨r, θ⟩, ⟨hr, _⟩, rfl⟩
      simpa [abs_of_pos (ha.trans_lt hr.1)] using hr
    · intro hz
      exact ⟨(‖z‖, z.arg), ⟨hz, mem_univ _⟩, norm_mul_exp_arg_mul_I z⟩
  rw [← he]
  exact hc.image _ hcont.continuousOn

/-- A positive-width neighborhood of a nonnegative radius is a connected circular domain. -/
theorem isConnected_norm_preimage_ball {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    IsConnected ((norm : ℂ → ℝ) ⁻¹' ball a δ) := by
  by_cases h : a < δ
  · have he : (norm : ℂ → ℝ) ⁻¹' ball a δ = ball 0 (a + δ) := by
      ext z
      simp only [mem_preimage, mem_ball, Real.dist_eq, dist_zero_right, abs_sub_lt_iff]
      constructor
      · intro hz; linarith
      · intro hz; constructor <;> linarith [norm_nonneg z]
    rw [he]
    exact isConnected_ball (by linarith)
  · have he : (norm : ℂ → ℝ) ⁻¹' ball a δ =
        {z : ℂ | a - δ < ‖z‖ ∧ ‖z‖ < a + δ} := by
      ext z
      simp only [mem_preimage, mem_ball, Real.dist_eq, mem_ofPred_eq, abs_sub_lt_iff]
      constructor <;> intro hz <;> constructor <;> linarith [hz.1, hz.2]
    rw [he]
    exact isConnected_complex_annulus (by linarith) (by linarith)

/-- Every point of an open Reinhardt set has a circular product neighborhood with connected factors.
The factors containing zero are discs. -/
theorem IsReinhardt.exists_circular_product_neighborhood {n : ℕ} {U : Set (Fin n → ℂ)}
    (hR : IsReinhardt U) (ho : IsOpen U) {z : Fin n → ℂ} (hz : z ∈ U) :
    ∃ V : Fin n → Set ℂ,
      (∀ i, IsOpen (V i)) ∧ (∀ i, IsConnected (V i)) ∧
      (∀ i, ∀ v ∈ V i, ∀ w : ℂ, ‖w‖ = ‖v‖ → w ∈ V i) ∧
      z ∈ Set.pi univ V ∧ Set.pi univ V ⊆ U := by
  have hz' : (fun i => (‖z i‖ : ℂ)) ∈ U := hR hz (fun i => by simp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho _ hz'
  let V : Fin n → Set ℂ := fun i => (norm : ℂ → ℝ) ⁻¹' ball ‖z i‖ δ
  refine ⟨V, fun i => isOpen_ball.preimage continuous_norm,
    fun i => isConnected_norm_preimage_ball (norm_nonneg _) hδ, ?_, ?_, ?_⟩
  · intro i v hv w hw
    change ‖w‖ ∈ ball ‖z i‖ δ
    rwa [hw]
  · intro i _
    exact mem_ball_self hδ
  · intro w hw
    apply hR (z := fun i => (‖w i‖ : ℂ)) (hball ?_) (fun i => by simp)
    rw [mem_ball, dist_pi_lt_iff hδ]
    intro i
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [V, mem_preimage, mem_ball, Real.dist_eq] using hw i (mem_univ _)

/-- Choose inner and outer coefficient circles and stricter evaluation bounds. At zero only the
upper evaluation bound is required. -/
theorem exists_circular_radii_bounds {V : Set ℂ} (ho : IsOpen V)
    (hrot : ∀ z ∈ V, ∀ w : ℂ, ‖w‖ = ‖z‖ → w ∈ V) {z : ℂ} (hz : z ∈ V) :
    ∃ a b t T : ℝ, 0 < a ∧ a < t ∧ 0 < T ∧ T < b ∧
      (a : ℂ) ∈ V ∧ (b : ℂ) ∈ V ∧ ‖z‖ < T ∧ (z ≠ 0 → t < ‖z‖) := by
  by_cases hz0 : z = 0
  · subst z
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho _ hz
    have hb : ((δ / 2 : ℝ) : ℂ) ∈ V := hball (by
      simpa [abs_of_pos hδ] using half_lt_self hδ)
    refine ⟨δ / 2, δ / 2, δ, δ / 4, by positivity, by linarith,
      by positivity, by linarith, hb, hb, ?_, ?_⟩
    · simp only [norm_zero]; positivity
    · simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hzV : (‖z‖ : ℂ) ∈ V := hrot z hz _ (by simp)
    obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      ((ho.preimage continuous_ofReal).mem_nhds hzV)
    obtain ⟨a, ha, haz⟩ := exists_between (max_lt hn hlu.1)
    obtain ⟨b, hzb, hb⟩ := exists_between hlu.2
    refine ⟨a, b, (a + ‖z‖) / 2, (‖z‖ + b) / 2,
      (le_max_left _ _).trans_lt ha, by linarith, by linarith, by linarith,
      hsub ⟨(le_max_right _ _).trans_lt ha, haz.trans hlu.2⟩,
      hsub ⟨hlu.1.trans hzb, hb⟩, by linarith, fun _ => by linarith⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
