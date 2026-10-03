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

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Topology.Connected.Clopen

/-! # Uniqueness on connected domains for locally smooth vector fields -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Local smoothness along one solution suffices for uniqueness on a
connected open time domain. No global Lipschitz constant is assumed. -/
theorem ode_eqOn_of_contDiffAt
    {v : E → E} {α β : ℝ → E} {T : Set ℝ}
    (hT : IsOpen T) (hconn : IsPreconnected T)
    (hv : ∀ t ∈ T, ContDiffAt ℝ 1 v (α t))
    (hα : ∀ t ∈ T, HasDerivAt α (v (α t)) t)
    (hβ : ∀ t ∈ T, HasDerivAt β (v (β t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ T) (hzero : α t₀ = β t₀) : EqOn α β T := by
  have hlocal (t : ℝ) (ht : t ∈ T) (he : α t = β t) : α =ᶠ[𝓝 t] β := by
    obtain ⟨L, V, hV, hLip⟩ := (hv t ht).exists_lipschitzOnWith
    have ha : ∀ᶠ s in 𝓝 t, HasDerivAt α (v (α s)) s := by
      filter_upwards [hT.mem_nhds ht] with s hs
      exact hα s hs
    have hb : ∀ᶠ s in 𝓝 t, HasDerivAt β (v (β s)) s := by
      filter_upwards [hT.mem_nhds ht] with s hs
      exact hβ s hs
    have hma := (hα t ht).continuousAt.preimage_mem_nhds hV
    have hmb := (hβ t ht).continuousAt.preimage_mem_nhds (by rwa [← he])
    exact ODE_solution_unique_of_eventually (Eventually.of_forall (fun _ => hLip))
      (ha.and hma) (hb.and hmb) he
  let S := {t | α t = β t} ∩ T
  suffices hsub : T ⊆ S from fun t ht => (hsub ht).1
  apply hconn.subset_of_closure_inter_subset (s := T) (u := S) _
    ⟨t₀, ⟨ht₀, ⟨hzero, ht₀⟩⟩⟩
  · change closure ({t | α t = β t} ∩ T) ∩ T ⊆ {t | α t = β t} ∩ T
    rw [inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_ofPred_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hα t ht).continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hβ t ht).continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t ht
    exact (hlocal t ht.2 ht.1).and (hT.mem_nhds ht.2)

end LichnerowiczObata
