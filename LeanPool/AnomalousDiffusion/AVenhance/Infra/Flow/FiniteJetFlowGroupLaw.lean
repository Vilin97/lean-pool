/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJetGlobal

/-! The recursively constructed jet flows obey the composition and inverse
identities of a genuine global flow. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

theorem FiniteJetFlowGroupLaw.spatialJetSolutions_unique_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ)
    {f g : ℝ → SpatialJetState n} (a d r : ℝ)
    (hr : r ∈ Ioo a d)
    (hf : ContinuousOn f (Icc a d))
    (hf' : ∀ q,
      HasDerivAt f (spatialJetField b n q (f q)) q)
    (hg : ContinuousOn g (Icc a d))
    (hg' : ∀ q,
      HasDerivAt g (spatialJetField b n q (g q)) q)
    (hinit : f r = g r) :
    ∀ t ∈ Icc a d, f t = g t := by
  let fcurve : Icc a d → SpatialJetState n := fun q => f q
  let gcurve : Icc a d → SpatialJetState n := fun q => g q
  have hfc : Continuous fcurve :=
    hf.comp_continuous continuous_subtype_val (fun q => q.2)
  have hgc : Continuous gcurve :=
    hg.comp_continuous continuous_subtype_val (fun q => q.2)
  have hfp : IsCompact (Set.range fcurve) := isCompact_range hfc
  have hgp : IsCompact (Set.range gcurve) := isCompact_range hgc
  obtain ⟨R, hR⟩ := hfp.isBounded.union hgp.isBounded |>.subset_closedBall (0 : SpatialJetState n)
  obtain ⟨K, hK⟩ := spatialJetField_lipschitzOnWith_on_window hb n a d 0 R
  have hmemf (q : ℝ) (hq : q ∈ Icc a d) : f q ∈ Metric.closedBall 0 R := by
    apply hR
    exact Or.inl ⟨⟨q, hq⟩, rfl⟩
  have hmemg (q : ℝ) (hq : q ∈ Icc a d) : g q ∈ Metric.closedBall 0 R := by
    apply hR
    exact Or.inr ⟨⟨q, hq⟩, rfl⟩
  have huniq := ODE_solution_unique_of_mem_Icc
    (v := spatialJetField b n) (s := fun _ => Metric.closedBall 0 R)
    (K := K) (f := f) (g := g) (a := a) (b := d) (t₀ := r)
    (fun q hq => hK q (Ioo_subset_Icc_self hq)) hr hf
    (fun q _ => hf' q) (fun q hq => hmemf q (Ioo_subset_Icc_self hq)) hg
    (fun q _ => hg' q) (fun q hq => hmemg q (Ioo_subset_Icc_self hq)) hinit
  intro t ht
  exact huniq ht

end

end AVenhance.Infra.Flow
