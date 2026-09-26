/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.MixedPartition

/-!
# The Eulerian-independence interface

Regts–Sevenster's Proposition 3: the Definition 5 summand of an
Eulerian edge subset does not depend on the choice of transition
system and orientation.  This Prop names the statement; it is
proved as `RS.eulerianIndependence` in
`RS/Novel/Skein/AllInternalAgreement.lean`.  `mixedValue_eq_summand`
eliminates the choice in `EdgeSubset.mixedValue` against any
concrete transition data.
-/

@[expose] public section

namespace RS

/-- The Eulerian-independence statement (Regts–Sevenster,
arXiv:1807.04494, Proposition 3): the mixed summand is independent
of the transition system and orientation.  Proved as
`RS.eulerianIndependence` in
`RS/Novel/Skein/AllInternalAgreement.lean`. -/
def EulerianIndependence : Prop :=
  ∀ {α : Type} {W : Fragment α} (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    {κ κ' : F.TransitionSystem}
    (o : κ.Orientation) (o' : κ'.Orientation),
    F.mixedSummand h o = F.mixedSummand h o'

/-- Under Eulerian independence, the choice-based value of an edge
subset equals the summand at any concrete transition data. -/
theorem EdgeSubset.mixedValue_eq_summand
    (hInd : EulerianIndependence)
    {α : Type} {W : Fragment α} (F : EdgeSubset W) {k ℓ : ℕ}
    (h : MixedFunctional k ℓ)
    {κ : F.TransitionSystem} (o : κ.Orientation) :
    F.mixedValue h = F.mixedSummand h o := by
  have hne : Nonempty ((κ' : F.TransitionSystem) × κ'.Orientation) :=
    ⟨⟨κ, o⟩⟩
  rw [EdgeSubset.mixedValue, dite_eq_left hne]
  exact hInd F h _ o

open Classical in
/-- **Transport invariance of the Definition 5 value**: under the
Eulerian-independence input, the choice-based value of a
transported edge subset is the original value. -/
theorem EdgeSubset.mixedValue_transport (hInd : EulerianIndependence)
    {α : Type} {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂)
    (F : EdgeSubset W₁) {k ℓ : ℕ} (h : MixedFunctional k ℓ) :
    (EdgeSubset.transport e F).mixedValue h = F.mixedValue h := by
  by_cases hne : Nonempty ((κ : F.TransitionSystem) × κ.Orientation)
  · obtain ⟨⟨κ, o⟩⟩ := hne
    rw [EdgeSubset.mixedValue_eq_summand hInd _ h
        (EdgeSubset.TransitionSystem.Orientation.transport e o),
      EdgeSubset.mixedValue_eq_summand hInd F h o]
    exact EdgeSubset.mixedSummand_transport e h o
  · have hne₂ : ¬ Nonempty
        ((κ : (EdgeSubset.transport e F).TransitionSystem) ×
          κ.Orientation) := by
      rintro ⟨⟨κ₂, o₂⟩⟩
      apply hne
      have hback : Nonempty
          ((κ' : (EdgeSubset.transport e.symm
              (EdgeSubset.transport e F)).TransitionSystem) ×
            κ'.Orientation) :=
        ⟨⟨κ₂.transport e.symm,
          EdgeSubset.TransitionSystem.Orientation.transport e.symm o₂⟩⟩
      rwa [EdgeSubset.transport_symm_transport] at hback
    rw [EdgeSubset.mixedValue, EdgeSubset.mixedValue,
      dite_eq_right hne, dite_eq_right hne₂]

open Classical in
/-- **Isomorphism invariance of the mixed partition function**:
under the Eulerian-independence input, equivalent fragments have
equal Definition 5 values. -/
theorem mixedPartition_transport (hInd : EulerianIndependence)
    {α : Type} {W₁ W₂ : Fragment α} (e : W₁.Equiv W₂)
    {k ℓ : ℕ} (h : MixedFunctional k ℓ) :
    mixedPartition h W₁ = mixedPartition h W₂ := by
  unfold mixedPartition
  rw [e.circles_eq]
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr e.flagEquiv) _ _ (fun s => ?_)
  rw [Equiv.finsetCongr_apply]
  have hpair : ∀ g : W₂.Flag, e.flagEquiv.symm (W₂.pairing g) =
      W₁.pairing (e.flagEquiv.symm g) := fun g => by
    apply e.flagEquiv.injective
    rw [Equiv.apply_symm_apply, e.pairing_comm, Equiv.apply_symm_apply]
  have hclosed : (∀ f ∈ s, W₁.pairing f ∈ s) ↔
      (∀ g ∈ s.map e.flagEquiv.toEmbedding,
        W₂.pairing g ∈ s.map e.flagEquiv.toEmbedding) := by
    constructor
    · intro hc g hg
      rw [Finset.mem_map_equiv] at hg ⊢
      rw [hpair]
      exact hc _ hg
    · intro hc f hf
      have hg := hc (e.flagEquiv f)
        (by rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]; exact hf)
      rwa [Finset.mem_map_equiv, hpair, Equiv.symm_apply_apply] at hg
  by_cases hc : ∀ f ∈ s, W₁.pairing f ∈ s
  · rw [dite_eq_left hc, dite_eq_left (hclosed.mp hc)]
    rw [show EdgeSubset.mk (s.map e.flagEquiv.toEmbedding)
          (hclosed.mp hc) =
        EdgeSubset.transport e (EdgeSubset.mk s hc)
      from EdgeSubset.ext rfl]
    simp only [EdgeSubset.transport_eulerian,
      EdgeSubset.mixedValue_transport hInd]
  · rw [dite_eq_right hc, dite_eq_right (fun hcc => hc (hclosed.mpr hcc))]

end RS
