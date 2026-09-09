/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Weak time continuity in `L²`

A Comparator solution is jointly smooth on the closed nonnegative time
half-space. Consequently its pairings with continuous compactly supported
test fields vary continuously, including at time zero. The uniform energy
bound and density of compactly supported continuous functions extend this
to all `L²` test fields. No spatial derivative integrability or energy
conservation assumption is used here.
-/

@[expose] public section


noncomputable section

open Set MeasureTheory
open scoped ContDiff Topology

namespace Euler.EulerExistenceAndSmoothnessR3

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

private theorem inner_toLp_eq_integral
    (a b : ℝ³ → ℝ³) (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, inner ℝ (a x) (b x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hax hbx
  rw [hax, hbx]

variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
  (h : EulerExistenceAndSmoothnessR3 u₀ v p)

include h

/-- Pairing the velocity with a continuous compactly supported test field is
continuous on the entire nonnegative time interval. -/
theorem velocity_test_pairing_continuousOn
    (φ : ℝ³ → ℝ³) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    ContinuousOn (fun t : ℝ => ∫ x : ℝ³, inner ℝ (φ x) (v x t)) (Ici 0) := by
  apply continuousOn_integral_of_compact_support hφc
  · apply (hφ.comp continuous_snd).continuousOn.inner
    exact h.velocity_smooth.continuousOn.comp continuous_swap.continuousOn
      (fun z hz => ⟨mem_univ _, hz.1⟩)
  · intro t x _ hx
    simp [image_eq_zero_of_notMem_tsupport hx]

/-- The natural velocity path in the Hilbert space `L²`. -/
def velocityLp (t : Ici (0 : ℝ)) : Lp ℝ³ 2 (volume : Measure ℝ³) :=
  (h.velocity_memLp t t.property).toLp (v · t)

theorem velocityLp_norm_sq (t : Ici (0 : ℝ)) :
    ‖h.velocityLp t‖ ^ 2 = ∫ x : ℝ³, ‖v x t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  unfold velocityLp
  rw [inner_toLp_eq_integral]
  simp only [real_inner_self_eq_norm_sq]

/-- The Comparator energy condition gives a uniform Hilbert space norm bound. -/
theorem velocityLp_norm_bounded :
    ∃ M : ℝ, 0 < M ∧ ∀ t : Ici (0 : ℝ), ‖h.velocityLp t‖ ≤ M := by
  obtain ⟨E, hE⟩ := h.globally_bounded_energy
  refine ⟨|E| + 1, by positivity, ?_⟩
  intro t
  have he : ‖h.velocityLp t‖ ^ 2 < E := by
    rw [h.velocityLp_norm_sq]
    exact hE t t.property
  have habs := le_abs_self E
  have habs0 := abs_nonneg E
  have hn := norm_nonneg (h.velocityLp t)
  nlinarith [sq_nonneg (|E|)]

/-- Every `L²` test pairing is continuous. This is weak time continuity of the
velocity in `L²`, derived from the exact Comparator hypotheses. -/
theorem velocityLp_weakly_continuous (φ : Lp ℝ³ 2 (volume : Measure ℝ³)) :
    Continuous (fun t : Ici (0 : ℝ) => inner ℝ φ (h.velocityLp t)) := by
  obtain ⟨M, hM, hbound⟩ := h.velocityLp_norm_bounded
  apply Metric.continuous_iff.2
  intro t₀ ε hε
  let δ : ℝ := ε / (4 * M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g, hgc, hgapprox, hgcont, hg⟩ :=
    (Lp.memLp φ).exists_hasCompactSupport_eLpNorm_sub_le
      (by norm_num : (2 : ENNReal) ≠ ⊤) (by positivity : ENNReal.ofReal δ ≠ 0)
  have happrox : ‖φ - hg.toLp g‖ ≤ δ := by
    have heq : ‖φ - hg.toLp g‖ =
        (eLpNorm ((φ : ℝ³ → ℝ³) - g) 2 volume).toReal := by
      conv_lhs => rw [← Lp.toLp_coeFn φ (Lp.memLp φ), ← MemLp.toLp_sub]
      exact Lp.norm_toLp _ _
    rw [heq]
    exact (ENNReal.toReal_mono (by simp) hgapprox).trans_eq (ENNReal.toReal_ofReal hδ.le)
  have hgpath : Continuous (fun t : Ici (0 : ℝ) =>
      inner ℝ (hg.toLp g) (h.velocityLp t)) := by
    have hc := continuousOn_iff_continuous_domRestrict.mp
      (h.velocity_test_pairing_continuousOn g hgcont hgc)
    change Continuous (fun t : Ici (0 : ℝ) => ∫ x : ℝ³, inner ℝ (g x) (v x t)) at hc
    simpa only [velocityLp, inner_toLp_eq_integral] using hc
  have herr (t : Ici (0 : ℝ)) :
      dist (inner ℝ φ (h.velocityLp t))
        (inner ℝ (hg.toLp g) (h.velocityLp t)) ≤ δ * M := by
    rw [dist_eq_norm, ← inner_sub_left]
    exact (norm_inner_le_norm _ _).trans (mul_le_mul happrox (hbound t)
      (norm_nonneg _) hδ.le)
  obtain ⟨η, hη, hηbound⟩ := (Metric.continuousAt_iff.mp hgpath.continuousAt)
    (ε / 2) (by positivity)
  refine ⟨η, hη, fun t ht => ?_⟩
  have hmid := hηbound ht
  have hlast := herr t₀
  rw [dist_comm] at hlast
  calc
    dist (inner ℝ φ (h.velocityLp t)) (inner ℝ φ (h.velocityLp t₀))
      ≤ dist (inner ℝ φ (h.velocityLp t)) (inner ℝ (hg.toLp g) (h.velocityLp t)) +
          dist (inner ℝ (hg.toLp g) (h.velocityLp t))
            (inner ℝ (hg.toLp g) (h.velocityLp t₀)) +
          dist (inner ℝ (hg.toLp g) (h.velocityLp t₀)) (inner ℝ φ (h.velocityLp t₀)) :=
        dist_triangle4 _ _ _ _
    _ < δ * M + ε / 2 + δ * M := by linarith [herr t]
    _ = ε := by dsimp [δ]; field_simp; ring

/-- Function-level form of weak `L²` continuity, without quotient representatives. -/
theorem velocity_pairing_continuousOn
    (φ : ℝ³ → ℝ³) (hφ : MemLp φ 2 volume) :
    ContinuousOn (fun t : ℝ => ∫ x : ℝ³, inner ℝ (φ x) (v x t)) (Ici 0) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun t : Ici (0 : ℝ) => ∫ x : ℝ³, inner ℝ (φ x) (v x t))
  simpa only [velocityLp, inner_toLp_eq_integral] using
    h.velocityLp_weakly_continuous (hφ.toLp φ)

/-- Every finite-energy test pairing attains the prescribed initial data weakly. -/
theorem velocity_pairing_tendsto_initial
    (φ : ℝ³ → ℝ³) (hφ : MemLp φ 2 volume) :
    Filter.Tendsto (fun t : ℝ => ∫ x : ℝ³, inner ℝ (φ x) (v x t))
      (𝓝[Ici 0] 0) (𝓝 (∫ x : ℝ³, inner ℝ (φ x) (u₀ x))) := by
  simpa only [ContinuousWithinAt, h.initial_condition] using
    h.velocity_pairing_continuousOn φ hφ 0 (by simp)

end Euler.EulerExistenceAndSmoothnessR3
