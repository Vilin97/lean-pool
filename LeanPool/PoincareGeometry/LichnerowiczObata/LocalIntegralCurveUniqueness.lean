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

/-
Copyright (c) 2023 Winston Yin. All rights reserved.
Adapted from Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique,
released under the Apache 2.0 license (https://www.apache.org/licenses/LICENSE-2.0).
The adaptation requires smoothness only along the first curve.
-/
module

public import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-! # Integral-curve uniqueness with local field regularity -/

@[expose] public section
open Set
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [I.Boundaryless] [T2Space M]

/-- Smoothness of the field near points on the first integral curve is
enough for uniqueness on an interval. No regularity away from that curve
is required. -/
theorem integralCurve_eqOn_of_contMDiffAt_range
    {V : (x : M) → TangentSpace I x} {γ γ' : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hV : ∀ t ∈ Ioo a b, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x => (⟨x, V x⟩ : TangentBundle I M)) (γ t))
    (hγ : IsMIntegralCurveOn γ V (Ioo a b))
    (hγ' : IsMIntegralCurveOn γ' V (Ioo a b)) (h : γ t₀ = γ' t₀) :
    EqOn γ γ' (Ioo a b) := by
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  suffices hsub : Ioo a b ⊆ s from fun t ht => (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact (hγ.continuousWithinAt ht).continuousAt (Ioo_mem_nhds ht.1 ht.2)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      apply ContinuousAt.comp _ continuousAt_subtype_val
      rw [Subtype.coe_mk]
      exact (hγ'.continuousWithinAt ht).continuousAt (Ioo_mem_nhds ht.1 ht.2)
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    have hmem := Ioo_mem_nhds ht.2.1 ht.2.2
    have heq : γ =ᶠ[𝓝 t] γ' := isMIntegralCurveAt_eventuallyEq_of_contMDiffAt
      (BoundarylessManifold.isInteriorPoint) (hV t ht.2)
      (hγ.isMIntegralCurveAt hmem) (hγ'.isMIntegralCurveAt hmem) ht.1
    exact (heq.and hmem).mono (fun _ h => h)

end LichnerowiczObata
