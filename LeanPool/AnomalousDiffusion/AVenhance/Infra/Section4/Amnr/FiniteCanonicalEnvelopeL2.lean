/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.LocalFiniteNormalOrder
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.CanonicalEnvelopeL2

/-! The canonical L2 envelope needs only the source finite regularity order. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4

/-- Summing only admissible canonical jets gives a finite L2 majorant with a
constant depending on the finite budget and cutoff, never on the source scale. -/
theorem amnrCanonicalEnvelope_finite_L2_le {U : Set AmnrSpace} (hU : IsOpen U)
    {μ : Measure AmnrSpace} (hμ : μ ≪ volume.restrict U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {N cut : ℕ}
    (hb : ContDiffOn ℝ N b U) (hf : ContDiffOn ℝ N f U) {S H G : ℝ} (hS : 0 < S) (hH : 0 < H)
    (hbound : ∀ α r, α.length + 2 * r ≤ N → r ≤ cut →
      eLpNorm (amnrWord b (amnrMixedWord α r) f) 2 μ ≤
        ENNReal.ofReal (G * amnrWeight S H (amnrMixedWord α r))) :
    eLpNorm (amnrCanonicalEnvelope N cut S H b f) 2 μ ≤
      ENNReal.ofReal ((amnrCanonicalSamples N cut).card * G) := by
  classical
  let F := fun q : List (Fin 2) × ℕ => fun z : AmnrSpace =>
    |amnrWord b (amnrMixedWord q.1 q.2) f z| / amnrWeight S H (amnrMixedWord q.1 q.2)
  have hterm (q : List (Fin 2) × ℕ) (hq : q ∈ amnrCanonicalSamples N cut) :
      eLpNorm (F q) 2 μ ≤ ENNReal.ofReal G := by
    have hq' := (amnrCanonicalSamples_mem q.1 q.2 N cut).mp hq
    have hlen := (amnrBudget_length_le (amnrMixedWord q.1 q.2)).trans
      (show amnrBudget (amnrMixedWord q.1 q.2) ≤ N by
        rw [amnrMixedWord_budget]; exact hq'.1)
    have hj := (amnrWord_contDiffOn hU hb hf (amnrMixedWord q.1 q.2)
      (n := 0) (by omega)).continuousOn
    have hm := (hj.aestronglyMeasurable hU.measurableSet (μ := volume)).mono_ac hμ
    have hW : 0 < amnrWeight S H (amnrMixedWord q.1 q.2) := by
      rw [amnrMixedWord_weight]
      positivity
    exact amnr_normalized_abs_L2_le hm hW (hbound q.1 q.2 hq'.1 hq'.2)
  have he : amnrCanonicalEnvelope N cut S H b f = ∑ q ∈ amnrCanonicalSamples N cut, F q := by
    funext z
    simp only [amnrCanonicalEnvelope, Finset.sum_apply, F]
  rw [he]
  refine (eLpNorm_sum_le (by norm_num : (1 : ENNReal) ≤ 2)).trans
    ((Finset.sum_le_sum hterm).trans_eq ?_)
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

end AVenhance.Infra.Section4
