/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.LedgerSets

/-!
# Per-step status identification of the relabel sets

Two composable identifications for the paired assembly.  First,
the pairs of a full pairwise-disjoint `AntiLowPair` list enumerate
the anti-canonical set: membership in the `pairFold` of such a
list is exactly being an end label of some anti-canonical chain
(`mem_pairFold_antiLow`) — the completeness direction pins every
anti flag's label as a first component by comparing cardinalities
(`Finset.eq_of_subset_of_card_le`).  Second, for the transported
frame of a separated step from a canonical source, the anti set's
end labels are exactly the labels whose high-status changed across
the repair (`antiLow_labels_eq_statusChange`): an anti end is
low-in-new but high-in-old, and its new partner is high-in-new but
low-in-old (the re-paired ends carry opposite old statuses,
`swap_dirs_opposite`); conversely a status-changed label must sit
on a re-paired end (`mem_highSet_repair_untouched`).
-/

namespace RS



/-! ## Propositional inequality helpers -/

namespace EdgeSubset

variable {α : Type}

/-! ## The enumeration lemma -/

section Enumeration

/-- The anti-canonical set consists of boundary flags. -/
theorem antiLowSet_subset_boundary
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) :
    antiLowSet o ⊆ F.boundaryFlags := by
  intro β h
  obtain ⟨hβ, -⟩ := mem_antiLowSet.mp h
  exact hβ

/-- **Pairs of a full disjoint anti-low list enumerate the anti
set**: for a list of anti-low pairs, pairwise disjoint and as long
as the anti set, membership in the fold is exactly being an end
label of some anti-canonical chain.  The completeness direction is
a counting argument: the first components form a `Nodup` list of
labels of anti flags, and label injectivity forces them to exhaust
the anti set. -/
theorem mem_pairFold_antiLow [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation}
    {L : List (α × α)}
    (hall : ∀ p ∈ L, AntiLowPair o p)
    (hdisj : L.Pairwise PairDisjoint)
    (hlen : L.length = (antiLowSet o).card) {a : α} :
    a ∈ pairFold L ↔
      ∃ (β : W.Flag) (hβ : β ∈ F.boundaryFlags),
        β ∈ antiLowSet o ∧
        (a = F.boundaryLabel hβ ∨
         a = F.boundaryLabel (κ.pathMatch_mem hβ)) := by
  classical
  -- the label image of the anti set
  have hinj : Set.InjOn
      (fun β : {x // x ∈ antiLowSet o} =>
        F.boundaryLabel (antiLowSet_subset_boundary o β.prop))
      (antiLowSet o).attach := by
    intro β _ γ _ hlab
    exact Subtype.ext (boundaryLabel_inj _ _ hlab)
  have hTcard :
      ((antiLowSet o).attach.image (fun β =>
        F.boundaryLabel
          (antiLowSet_subset_boundary o β.prop))).card =
        (antiLowSet o).card :=
    (Finset.card_image_of_injOn hinj).trans Finset.card_attach
  have hmemT : ∀ (γ : W.Flag) (hm : γ ∈ antiLowSet o),
      F.boundaryLabel (antiLowSet_subset_boundary o hm) ∈
        (antiLowSet o).attach.image (fun β =>
          F.boundaryLabel
            (antiLowSet_subset_boundary o β.prop)) := by
    intro γ hm
    exact Finset.mem_image.mpr
      ⟨⟨γ, hm⟩, Finset.mem_attach _ _, rfl⟩
  -- the first components exhaust the label image
  have hnd : (L.map Prod.fst).Nodup :=
    hdisj.map Prod.fst (fun p q hpq => hpq.1)
  have hFscard : (L.map Prod.fst).toFinset.card = L.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  have hFsub : (L.map Prod.fst).toFinset ⊆
      (antiLowSet o).attach.image (fun β =>
        F.boundaryLabel
          (antiLowSet_subset_boundary o β.prop)) := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hx
    obtain ⟨β, hβ, hm, h1, -⟩ := hall p hp
    rw [← hpx, h1]
    exact hmemT β hm
  have hFeq : (L.map Prod.fst).toFinset =
      (antiLowSet o).attach.image (fun β =>
        F.boundaryLabel
          (antiLowSet_subset_boundary o β.prop)) :=
    Finset.eq_of_subset_of_card_le hFsub
      (le_of_eq (by rw [hTcard, hFscard, ← hlen]))
  rw [mem_pairFold_of_pairwise hdisj]
  -- ═══════ AN ANTI END IS A STATUS CHANGE ═══════
  -- Forward: the four re-paired ends, one case each.  Backward: a
  -- changed label must sit on one of them.
  constructor
  · rintro ⟨p, hp, hpa⟩
    obtain ⟨β, hβ, hm, h1, h2⟩ := hall p hp
    rcases hpa with rfl | rfl
    · exact ⟨β, hβ, hm, Or.inl h1⟩
    · exact ⟨β, hβ, hm, Or.inr h2⟩
  · rintro ⟨β, hβ, hm, hpa⟩
    have hlT : F.boundaryLabel hβ ∈ (L.map Prod.fst).toFinset := by
      rw [hFeq]
      exact hmemT β hm
    rw [List.mem_toFinset] at hlT
    obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hlT
    obtain ⟨β', hβ', -, h1, h2⟩ := hall p hp
    have hββ' : β' = β :=
      boundaryLabel_inj hβ' hβ (h1.symm.trans hp1)
    have hpm2 : p.2 = F.boundaryLabel (κ.pathMatch_mem hβ) :=
      h2.trans (boundaryLabel_congr (κ.pathMatch_mem hβ')
        (κ.pathMatch_mem hβ) (κ.pathMatch_congr hββ' hβ' hβ))
    refine ⟨p, hp, ?_⟩
    rcases hpa with rfl | rfl
    · exact Or.inl hp1.symm
    · exact Or.inr hpm2.symm

end Enumeration

/-! ## The separated-step status identification -/

section StepStatus

/-- **An anti end and its new partner both change status**: from a
canonical source, a flag `x` that is anti-canonical for the
transported frame is high-in-old and low-in-new, while its new
partner `y` is low-in-old (the re-paired ends carry opposite old
directions) and high-in-new. -/
private theorem status_flip_anti_end
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {x y : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hy : y ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags)
    (hinty : W.pairing y ∈ F.internalFlags)
    (hxy : (κ.repair a b c d v hsq).pathMatch x hx = y)
    (hanti : x ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq o
        hflip)) :
    ((F.boundaryLabel hx ∈ highSet (κ.repair a b c d v hsq)) ≠
        (F.boundaryLabel hx ∈ highSet κ)) ∧
      ((F.boundaryLabel hy ∈ highSet (κ.repair a b c d v hsq)) ≠
        (F.boundaryLabel hy ∈ highSet κ)) := by
  obtain ⟨hlt, hhigh⟩ :=
    (mem_antiLowSet_transport_of_canonical hsq hflip hc hx hy
      hintx hxy).mp hanti
  have hyx : (κ.repair a b c d v hsq).pathMatch y hy = x :=
    ((κ.repair a b c d v hsq).pathMatch_congr hxy.symm hy
      ((κ.repair a b c d v hsq).pathMatch_mem hx)).trans
      ((κ.repair a b c d v hsq).pathMatch_invol hx)
  have hdx : chainDir o x = true :=
    (chainDir_true_iff_high hc hx hintx).mpr hhigh
  have hdy : chainDir o y = false := by
    have h := swap_dirs_opposite hsq o hflip hx hxy hintx
    rw [hdx, Bool.not_true] at h
    exact h
  have hylow : ¬ F.boundaryLabel (κ.pathMatch_mem hy) <
      F.boundaryLabel hy := by
    intro hlt'
    have h := (chainDir_true_iff_high hc hy hinty).mpr hlt'
    rw [hdy] at h
    exact Bool.false_ne_true h
  constructor
  · refine prop_ne_of_right ?_ ?_
    · rw [mem_highSet_repair_end hsq hx hy hintx hxy]
      exact lt_asymm hlt
    · rw [mem_highSet_iff_lt hx hintx]
      exact hhigh
  · refine prop_ne_of_left ?_ ?_
    · rw [mem_highSet_repair_end hsq hy hx hinty hyx]
      exact hlt
    · rw [mem_highSet_iff_lt hy hinty]
      exact hylow

/-- The forward case handler: any end label of an anti-canonical
re-paired chord is a status-changed label. -/
private theorem statusChange_end_fwd
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {x y : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hy : y ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags)
    (hinty : W.pairing y ∈ F.internalFlags)
    (hxy : (κ.repair a b c d v hsq).pathMatch x hx = y)
    (hanti : x ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq o
        hflip))
    {i : α}
    (hi : i = F.boundaryLabel hx ∨
      i = F.boundaryLabel
        ((κ.repair a b c d v hsq).pathMatch_mem hx)) :
    (i ∈ highSet (κ.repair a b c d v hsq)) ≠ (i ∈ highSet κ) := by
  obtain ⟨hchx, hchy⟩ := status_flip_anti_end hsq hflip hc hx hy
    hintx hinty hxy hanti
  rcases hi with rfl | rfl
  · exact hchx
  · rwa [boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hx) hy hxy]

/-- The backward case handler: if the status of a re-paired end's
label changed, then either that end is anti-canonical for the
transported frame (it was high, now low) and the label is its own,
or its new partner is (the end was low, now high) and the label is
the partner's partner-label. -/
private theorem statusChange_end_bwd
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {x y : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hy : y ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags)
    (hinty : W.pairing y ∈ F.internalFlags)
    (hxy : (κ.repair a b c d v hsq).pathMatch x hx = y)
    (hch :
      (F.boundaryLabel hx ∈ highSet (κ.repair a b c d v hsq)) ≠
        (F.boundaryLabel hx ∈ highSet κ)) :
    ∃ (β : W.Flag) (hβ : β ∈ F.boundaryFlags),
      β ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) ∧
      (F.boundaryLabel hx = F.boundaryLabel hβ ∨
       F.boundaryLabel hx = F.boundaryLabel
         ((κ.repair a b c d v hsq).pathMatch_mem hβ)) := by
  have hyx : (κ.repair a b c d v hsq).pathMatch y hy = x :=
    ((κ.repair a b c d v hsq).pathMatch_congr hxy.symm hy
      ((κ.repair a b c d v hsq).pathMatch_mem hx)).trans
      ((κ.repair a b c d v hsq).pathMatch_invol hx)
  have hxney : x ≠ y := fun h =>
    (κ.repair a b c d v hsq).pathMatch_ne_self hx
      (hxy.trans h.symm)
  have hlabne : F.boundaryLabel hx ≠ F.boundaryLabel hy :=
    fun h => hxney (boundaryLabel_inj hx hy h)
  rw [mem_highSet_repair_end hsq hx hy hintx hxy,
    mem_highSet_iff_lt hx hintx] at hch
  rcases prop_ne_cases hch with ⟨hnew, hold⟩ | ⟨hnew, hold⟩
  · -- `x` is high-in-new and was low-in-old: its partner `y` was
    -- high-in-old and is low-in-new, so `y` is the anti end.
    have hdx : chainDir o x = false := by
      cases hd : chainDir o x
      · rfl
      · exact absurd ((chainDir_true_iff_high hc hx hintx).mp hd)
          hold
    have hdy := swap_dirs_opposite hsq o hflip hx hxy hintx
    rw [hdx, Bool.not_false] at hdy
    have hyhigh : F.boundaryLabel (κ.pathMatch_mem hy) <
        F.boundaryLabel hy :=
      (chainDir_true_iff_high hc hy hinty).mp hdy
    have hymem : y ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) :=
      (mem_antiLowSet_transport_of_canonical hsq hflip hc hy hx
        hinty hyx).mpr ⟨hnew, hyhigh⟩
    exact ⟨y, hy, hymem, Or.inr
      (boundaryLabel_congr
        ((κ.repair a b c d v hsq).pathMatch_mem hy) hx
        hyx).symm⟩
  · -- `x` was high-in-old and is low-in-new: `x` is the anti end.
    have hlt : F.boundaryLabel hx < F.boundaryLabel hy :=
      lt_of_le_of_ne (not_lt.mp hnew) hlabne
    have hxmem : x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) :=
      (mem_antiLowSet_transport_of_canonical hsq hflip hc hx hy
        hintx hxy).mpr ⟨hlt, hold⟩
    exact ⟨x, hx, hxmem, Or.inl rfl⟩

/-- **The separated-step status identification**: for the
transported frame of a separated step from a canonical source, the
end labels of the anti-canonical chords — each anti low end with
its partner in the *repaired* system, the shape produced by
`mem_pairFold_antiLow` at the transported frame — are exactly the
labels whose high-status differs between the repaired and the
source systems. -/
theorem antiLow_labels_eq_statusChange
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hcross : (κ.repair a b c d v hsq).pathMatch e₁ he₁ = e₂)
    (hfar : (κ.repair a b c d v hsq).pathMatch
        (κ.pathMatch e₁ he₁) (κ.pathMatch_mem he₁) =
      κ.pathMatch e₂ he₂)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
      δ ≠ κ.pathMatch e₂ he₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ)
    (hint₁ : W.pairing e₁ ∈ F.internalFlags)
    (hint₂ : W.pairing e₂ ∈ F.internalFlags)
    (hintP₁ : W.pairing (κ.pathMatch e₁ he₁) ∈ F.internalFlags)
    (hintP₂ : W.pairing (κ.pathMatch e₂ he₂) ∈ F.internalFlags)
    {i : α} :
    (∃ (β : W.Flag) (hβ : β ∈ F.boundaryFlags),
        β ∈ antiLowSet
          (RelTransitionSystem.Orientation.transportRepair hsq o
            hflip) ∧
        (i = F.boundaryLabel hβ ∨
         i = F.boundaryLabel
           ((κ.repair a b c d v hsq).pathMatch_mem hβ))) ↔
      ((i ∈ highSet (κ.repair a b c d v hsq)) ≠
        (i ∈ highSet κ)) := by
  have hcross₂ : (κ.repair a b c d v hsq).pathMatch e₂ he₂ = e₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hcross.symm he₂
      ((κ.repair a b c d v hsq).pathMatch_mem he₁)).trans
      ((κ.repair a b c d v hsq).pathMatch_invol he₁)
  have hfar₂ : (κ.repair a b c d v hsq).pathMatch
      (κ.pathMatch e₂ he₂) (κ.pathMatch_mem he₂) =
      κ.pathMatch e₁ he₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hfar.symm
      (κ.pathMatch_mem he₂)
      ((κ.repair a b c d v hsq).pathMatch_mem
        (κ.pathMatch_mem he₁))).trans
      ((κ.repair a b c d v hsq).pathMatch_invol
        (κ.pathMatch_mem he₁))
  -- ═══════ AN ANTI END IS A STATUS CHANGE ═══════
  -- Forward: the four re-paired ends, one case each.  Backward: a
  -- changed label must sit on one of them.
  constructor
  · rintro ⟨β, hβ, hmem, hlab⟩
    have hfour := antiLowSet_transport_subset hsq hflip hc he₁
      he₂ hout hmem
    rcases Finset.mem_insert.mp hfour with h | hfour₁
    · -- `β = e₁`, new partner `e₂`
      have hintβ : W.pairing β ∈ F.internalFlags := by
        rw [h]
        exact hint₁
      have hxy : (κ.repair a b c d v hsq).pathMatch β hβ = e₂ :=
        ((κ.repair a b c d v hsq).pathMatch_congr h hβ he₁).trans
          hcross
      exact statusChange_end_fwd hsq hflip hc hβ he₂ hintβ hint₂
        hxy hmem hlab
    rcases Finset.mem_insert.mp hfour₁ with h | hfour₂
    · -- `β = e₂`, new partner `e₁`
      have hintβ : W.pairing β ∈ F.internalFlags := by
        rw [h]
        exact hint₂
      have hxy : (κ.repair a b c d v hsq).pathMatch β hβ = e₁ :=
        ((κ.repair a b c d v hsq).pathMatch_congr h hβ he₂).trans
          hcross₂
      exact statusChange_end_fwd hsq hflip hc hβ he₁ hintβ hint₁
        hxy hmem hlab
    rcases Finset.mem_insert.mp hfour₂ with h | hfour₃
    · -- `β = κ.pathMatch e₁`, new partner `κ.pathMatch e₂`
      have hintβ : W.pairing β ∈ F.internalFlags := by
        rw [h]
        exact hintP₁
      have hxy : (κ.repair a b c d v hsq).pathMatch β hβ =
          κ.pathMatch e₂ he₂ :=
        ((κ.repair a b c d v hsq).pathMatch_congr h hβ
          (κ.pathMatch_mem he₁)).trans hfar
      exact statusChange_end_fwd hsq hflip hc hβ
        (κ.pathMatch_mem he₂) hintβ hintP₂ hxy hmem hlab
    · -- `β = κ.pathMatch e₂`, new partner `κ.pathMatch e₁`
      have h := Finset.mem_singleton.mp hfour₃
      have hintβ : W.pairing β ∈ F.internalFlags := by
        rw [h]
        exact hintP₂
      have hxy : (κ.repair a b c d v hsq).pathMatch β hβ =
          κ.pathMatch e₁ he₁ :=
        ((κ.repair a b c d v hsq).pathMatch_congr h hβ
          (κ.pathMatch_mem he₂)).trans hfar₂
      exact statusChange_end_fwd hsq hflip hc hβ
        (κ.pathMatch_mem he₁) hintβ hintP₁ hxy hmem hlab
  · intro hchanged
    -- a status-changed label is the label of a participating flag
    have hpart : ∃ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        W.pairing δ ∈ F.internalFlags ∧
        F.boundaryLabel hδ = i := by
      rcases prop_ne_cases hchanged with ⟨hnew, -⟩ | ⟨-, hold⟩
      · obtain ⟨δ, hδ, hint, -, hlab⟩ := mem_highSet.mp hnew
        exact ⟨δ, hδ, hint, hlab⟩
      · obtain ⟨δ, hδ, hint, -, hlab⟩ := mem_highSet.mp hold
        exact ⟨δ, hδ, hint, hlab⟩
    obtain ⟨δ, hδ, hintδ, hlabδ⟩ := hpart
    subst hlabδ
    by_cases h1 : δ = e₁
    · rw [boundaryLabel_congr hδ he₁ h1] at hchanged ⊢
      exact statusChange_end_bwd hsq hflip hc he₁ he₂ hint₁ hint₂
        hcross hchanged
    by_cases h2 : δ = e₂
    · rw [boundaryLabel_congr hδ he₂ h2] at hchanged ⊢
      exact statusChange_end_bwd hsq hflip hc he₂ he₁ hint₂ hint₁
        hcross₂ hchanged
    by_cases h3 : δ = κ.pathMatch e₁ he₁
    · rw [boundaryLabel_congr hδ (κ.pathMatch_mem he₁) h3]
        at hchanged ⊢
      exact statusChange_end_bwd hsq hflip hc
        (κ.pathMatch_mem he₁) (κ.pathMatch_mem he₂) hintP₁ hintP₂
        hfar hchanged
    by_cases h4 : δ = κ.pathMatch e₂ he₂
    · rw [boundaryLabel_congr hδ (κ.pathMatch_mem he₂) h4]
        at hchanged ⊢
      exact statusChange_end_bwd hsq hflip hc
        (κ.pathMatch_mem he₂) (κ.pathMatch_mem he₁) hintP₂ hintP₁
        hfar₂ hchanged
    · -- untouched flags keep their status: contradiction
      exact absurd (propext (mem_highSet_repair_untouched hsq he₁
        he₂ hout hδ hintδ h1 h2 h3 h4)) hchanged

end StepStatus

end EdgeSubset

/-- Propositional inequality as an exclusive disjunction, in the
`symmU` component order. -/
theorem prop_ne_iff {P Q : Prop} :
    (P ≠ Q) ↔ ((P ∧ ¬Q) ∨ (Q ∧ ¬P)) := by
  constructor
  · intro h
    rcases prop_ne_cases h with ⟨hP, hQ⟩ | ⟨hP, hQ⟩
    · exact Or.inl ⟨hP, hQ⟩
    · exact Or.inr ⟨hQ, hP⟩
  · rintro (⟨hP, hQ⟩ | ⟨hQ, hP⟩)
    · exact prop_ne_of_left hP hQ
    · exact prop_ne_of_right hP hQ

end RS
