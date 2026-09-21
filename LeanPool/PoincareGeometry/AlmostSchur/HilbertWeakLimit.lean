/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual

/-! # Representing limits of pairings of a bounded Hilbert-space family -/

@[expose] public noncomputable section
open Filter Set
open scoped Topology

namespace AlmostSchur

/-- A bounded family has a weak cluster representative, which represents every
convergent scalar pairing. No sequential compactness assumption is needed. -/
theorem exists_hilbert_pairing_limit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (l : Filter ι) [l.NeBot] (d : ι → H) (C : ℝ)
    (hb : ∀ᶠ i in l, ‖d i‖ ≤ C) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ v : H, ∀ b : ℝ,
      Tendsto (fun i => inner ℝ (d i) v) l (𝓝 b) → inner ℝ g v = b := by
  let T : H → WeakDual ℝ H := fun x => (InnerProductSpace.toDual ℝ H x).toWeakDual
  have hT : ∀ᶠ i in l,
      T (d i) ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) C := by
    filter_upwards [hb] with i hi
    simpa [T, Metric.mem_closedBall, dist_zero_right] using hi
  obtain ⟨w, hw, hc⟩ := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) C).exists_mapClusterPt
    (show Filter.map (T ∘ d) l ≤ 𝓟 (WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℝ H) C) from le_principal_iff.mpr hT)
  let g := (InnerProductSpace.toDual ℝ H).symm w.toStrongDual
  refine ⟨g, ?_, ?_⟩
  · have hn : ‖w.toStrongDual‖ ≤ C := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    simpa [g] using hn
  · intro v b hb
    have he := hc.continuousAt_comp (WeakDual.eval_continuous v).continuousAt
    have hp : MapClusterPt (w v) l (fun i => inner ℝ (d i) v) := by
      simpa [T, Function.comp_def] using he
    have : NeBot (𝓝 (w v) ⊓ Filter.map (fun i => inner ℝ (d i) v) l) := hp
    have eq : w v = b := tendsto_nhds_unique
      (show Tendsto id (𝓝 (w v) ⊓ Filter.map (fun i => inner ℝ (d i) v) l)
        (𝓝 (w v)) from inf_le_left)
      (show Tendsto id (𝓝 (w v) ⊓ Filter.map (fun i => inner ℝ (d i) v) l)
        (𝓝 b) from le_trans inf_le_right hb)
    simpa [g] using eq

end AlmostSchur
