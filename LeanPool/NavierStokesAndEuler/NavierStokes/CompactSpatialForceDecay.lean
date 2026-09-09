/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ComparatorBridge

@[expose] public section

/-!
# Space-time decay from compact spatial and future time support

Unlike the periodic force bound, these estimates use one compact subset of
Euclidean space. They bound the full one-sided space-time derivative tensors,
including time zero, and allow every real decay exponent.
-/

noncomputable section

namespace NavierStokes.CompactSpatialForceDecay

open Set Filter Function ProblemStatement
open scoped ContDiff Topology

/-- A single spatial support set works at every physical time. -/
def SupportedIn (K : Set Space) (f : VelocityField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ x : Space, x ∉ K → f (t, x) = 0

theorem jet_zero_outside {K : Set Space} (hK : IsClosed K) {f : VelocityField}
    (hf : SupportedIn K f) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) {x : Space} (hx : x ∉ K) :
    iteratedFDerivWithin ℝ m f futureDomain (t, x) = 0 := by
  have he : f =ᶠ[𝓝[futureDomain] (t, x)] (fun _ => 0) := by
    have hU : {z : SpaceTime | z.2 ∉ K} ∈ 𝓝 (t, x) :=
      (hK.isOpen_compl.preimage continuous_snd).mem_nhds hx
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU, self_mem_nhdsWithin] with z hz hd
    exact hf z.1 hd.1 z.2 hz
  simpa using he.iteratedFDerivWithin_eq (hf t ht x hx) m (𝕜 := ℝ)

theorem jet_zero_after {f : VelocityField} {T : ℝ}
    (hf : ∀ t : ℝ, T ≤ t → ∀ x : Space, f (t, x) = 0)
    (m : ℕ) {t : ℝ} (ht : T < t) (x : Space) :
    iteratedFDerivWithin ℝ m f futureDomain (t, x) = 0 := by
  have he : f =ᶠ[𝓝[futureDomain] (t, x)] (fun _ => 0) := by
    have hU : {z : SpaceTime | T < z.1} ∈ 𝓝 (t, x) :=
      (isOpen_lt continuous_const continuous_fst).mem_nhds ht
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU] with z hz
    exact hf z.1 hz.le z.2
  simpa using he.iteratedFDerivWithin_eq (hf t ht.le x) m (𝕜 := ℝ)

/-- Compactness bounds the weighted jet itself, so no restriction on `K` is needed. -/
theorem jet_decay {S : Set Space} (hS : IsCompact S) {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (hs : SupportedIn S f)
    (htime : CompactFutureTimeSupport f) (m : ℕ) (K : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      ‖iteratedFDerivWithin ℝ m f futureDomain (t, x)‖ ≤ C / (1 + ‖x‖ + t) ^ K := by
  obtain ⟨T, hT, hz⟩ := htime
  let J := iteratedFDerivWithin ℝ m f futureDomain
  have hj : ContinuousOn J futureDomain :=
    hf.continuousOn_iteratedFDerivWithin
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m).le
      ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ)
  have hsub : Icc (0 : ℝ) (T + 1) ×ˢ S ⊆ futureDomain :=
    fun _ h => ⟨h.1.1, mem_univ _⟩
  have hw : ContinuousOn (fun z : SpaceTime => (1 + ‖z.2‖ + z.1) ^ K)
      (Icc (0 : ℝ) (T + 1) ×ˢ S) := by
    apply ((continuous_const.add continuous_snd.norm).add continuous_fst).continuousOn.rpow_const
    intro z hz
    left
    change 1 + ‖z.2‖ + z.1 ≠ 0
    have htz : 0 ≤ z.1 := hz.1.1
    exact ne_of_gt (by linarith [norm_nonneg z.2])
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod hS).exists_bound_of_continuousOn
    (((hj.mono hsub).norm).mul hw)
  refine ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro t ht x
  have hp : 0 < (1 + ‖x‖ + t) ^ K := Real.rpow_pos_of_pos (by positivity) K
  by_cases hx : x ∈ S
  · by_cases htt : t ≤ T + 1
    · apply (le_div_iff₀ hp).mpr
      have hb := hM (t, x) ⟨⟨ht, htt⟩, hx⟩
      exact (le_abs_self _).trans (hb.trans (le_max_left _ _))
    · rw [jet_zero_after hz m (by linarith) x, norm_zero]
      exact le_of_lt (div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hp)
  · rw [jet_zero_outside hS.isClosed hs m ht hx, norm_zero]
    exact le_of_lt (div_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) hp)

theorem rescale_supported {S : Set Space} {f : VelocityField} (hf : SupportedIn S f)
    (a : ℝ) {c : ℝ} (hc : 0 ≤ c) : SupportedIn S (ComparatorBridge.rescale a c f) := by
  intro t ht x hx
  simp only [ComparatorBridge.rescale, hf (c * t) (mul_nonneg hc ht) x hx, smul_zero]

theorem forceConditionDecay {S : Set Space} (hS : IsCompact S) {f : VelocityField}
    (hf : ContDiffOn ℝ ∞ f futureDomain) (hs : SupportedIn S f)
    (htime : CompactFutureTimeSupport f) :
    Comparator.ForceConditionDecay (ComparatorBridge.toComparator f) := by
  refine ⟨⟨ComparatorBridge.toComparator_smooth hf⟩, ?_⟩
  intro m K
  obtain ⟨C, _, hb⟩ := jet_decay hS hf hs htime m K
  refine ⟨C, ?_⟩
  intro x t ht
  rw [ComparatorBridge.toComparator_jet_norm f m x ht]
  exact hb t ht x

end NavierStokes.CompactSpatialForceDecay
