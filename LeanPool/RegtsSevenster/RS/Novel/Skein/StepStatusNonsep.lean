/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StepStatus

/-!
# The non-separated per-step status identification

The non-separated counterpart of `antiLow_labels_eq_statusChange`:
for the transported frame of a non-separated step — reached from a
canonical source `o` by first flipping the anchor chain (the
`c`-chain, realized as a `PortedFlipSet`) and then transporting
across the repair — the fold of the anchor pair with a full
disjoint anti-low list is exactly the status-change set
(`nonsep_labels_eq_statusChange`).

The identification dissolves into a per-chord XOR computation.  For
a participating end `x` the chain flip toggles the direction
exactly when `x` is an end of the anchor chord
(`pairing_mem_flipSet_iff`, via chain disjointness), so with
`T := x on the anchor chord`, `old := high-in-κ`,
`new := high-in-κ'`:

* `x` or its new partner is anti-canonical for the transported
  frame iff `new ⊕ (old ⊕ T)` — the new-chord rigidity pairs the
  two ends' directions (`anti_ends_iff_toggle_xor_status`);
* the anchor membership contributes `T` once more, and
  `T ⊕ (new ⊕ old ⊕ T) = new ⊕ old` is the status change —
  the `(2,3)`-chord phenomenon (an anchor end whose status did not
  change must be anti: the extra toggle needs undoing) is the case
  `T = true`, `new = old` of the same algebra.

No swap-end data is consumed: the identity holds for the anchored
transported frame of *any* repair from a canonical source.
-/

namespace RS

open scoped Classical

/-! ## Propositional XOR helpers -/

/-- XOR of propositions rotates. -/
private theorem prop_xor_rotate {P Q R : Prop} :
    (P ≠ (Q ≠ R)) ↔ (R ≠ (P ≠ Q)) := by
  simp only [prop_ne_iff]
  tauto

/-- XOR of propositions cancels a repeated argument. -/
private theorem prop_xor_cancel {P Q : Prop} :
    (P ≠ (P ≠ Q)) ↔ Q := by
  simp only [prop_ne_iff]
  tauto

namespace EdgeSubset

variable {α : Type}

/-! ## The toggle set of the anchored chain flip -/

section ToggleSet

/-- **The chain flip toggles exactly the anchor chord's ends**: a
ported flip set realized by the boundary chain of `β₂` contains the
entry edge of a participating boundary flag `x` iff `x` is an end
of `β₂`'s chord.  The two anchor ends' entry edges lie on the chain
by construction; any other participating end's entry edge is on a
genuinely distinct chain (`onBoundaryChain_disjoint`). -/
theorem pairing_mem_flipSet_iff
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {S : Finset W.Flag} {p₁ p₂ : W.Flag} {i₁ i₂ : α}
    (_ : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {β₂ : W.Flag} (hβ₂ : β₂ ∈ F.boundaryFlags)
    (hint₂ : W.pairing β₂ ∈ F.internalFlags)
    (honS : ∀ f ∈ S, OnBoundaryChain κ β₂ f)
    (hSon : ∀ f ∈ F.internalFlags,
      OnBoundaryChain κ β₂ f → f ∈ S)
    {x : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hxint : W.pairing x ∈ F.internalFlags) :
    W.pairing x ∈ S ↔ (x = β₂ ∨ x = κ.pathMatch β₂ hβ₂) := by
  obtain ⟨kc, -, hcont, hterm⟩ :=
    chain_terminates_with_data κ hβ₂
  have hpm : κ.pathMatch β₂ hβ₂ =
      W.pairing (iterWalk κ β₂ kc) :=
    pathMatch_eq_of_chain κ hβ₂ hcont hterm
  constructor
  · intro hmem
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨kx, -, hcontx, htermx⟩ :=
      chain_terminates_with_data κ hx
    exact onBoundaryChain_disjoint hβ₂ hx h1 h2 (honS _ hmem)
      ⟨kx, 0, Nat.zero_le kx, hcontx, htermx,
        Or.inr (by rw [iterWalk_zero])⟩
  · rintro (rfl | rfl)
    · exact hSon _ hint₂
        ⟨kc, 0, Nat.zero_le kc, hcont, hterm,
          Or.inr (by rw [iterWalk_zero])⟩
    · apply hSon _ hxint
      refine ⟨kc, kc, le_rfl, hcont, hterm, Or.inl ?_⟩
      rw [hpm, W.pairing_invol]

end ToggleSet

/-! ## The per-end evaluation of the anchored transported frame -/

section StepStatusNonsep

/-- **The per-chord XOR evaluation**: for a participating boundary
end `x`, some end of `x`'s *new* chord is anti-canonical for the
anchored transported frame iff the direction toggle at `x` (entry
edge in the flip set) differs from the status change of `x`'s
label.  From the canonical source the old direction at `x` is its
old high-status; the flip XORs the toggle in; the new-chord
rigidity pairs the two ends' directions, so exactly the low end of
an "old-dir-still-up" chord is anti — the XOR of new-status with
toggled old-status. -/
private theorem anti_ends_iff_toggle_xor_status
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    {S : Finset W.Flag} {p₁ p₂ : W.Flag} {i₁ i₂ : α}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hc : PathCanonical o)
    (hpf : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hflip : (o.portFlip hpf).isOut c = !(o.portFlip hpf).isOut a)
    {x : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hxint : W.pairing x ∈ F.internalFlags) :
    (x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq
          (o.portFlip hpf) hflip) ∨
      (κ.repair a b c d v hsq).pathMatch x hx ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq
          (o.portFlip hpf) hflip)) ↔
      ((W.pairing x ∈ S) ≠
        ((F.boundaryLabel hx ∈ highSet (κ.repair a b c d v hsq)) ≠
          (F.boundaryLabel hx ∈ highSet κ))) := by
  -- ═══════ SETUP: THE PARTNER AND THE TWO LABELS ═══════
  have hy : (κ.repair a b c d v hsq).pathMatch x hx ∈
      F.boundaryFlags := (κ.repair a b c d v hsq).pathMatch_mem hx
  have hyint : W.pairing
      ((κ.repair a b c d v hsq).pathMatch x hx) ∈
      F.internalFlags :=
    pathMatch_pairing_internal (κ := κ.repair a b c d v hsq) hx
      hxint
  have hinv : (κ.repair a b c d v hsq).pathMatch
      ((κ.repair a b c d v hsq).pathMatch x hx) hy = x :=
    (κ.repair a b c d v hsq).pathMatch_invol hx
  have hlabne : F.boundaryLabel hx ≠
      F.boundaryLabel
        ((κ.repair a b c d v hsq).pathMatch_mem hx) :=
    fun h => (κ.repair a b c d v hsq).pathMatch_ne_self hx
      (boundaryLabel_inj
        ((κ.repair a b c d v hsq).pathMatch_mem hx) hx h.symm)
  -- ═══════ STAGE 1: THE TWO ANTI MEMBERSHIPS ═══════
  -- the two anti memberships, at the preserved directions
  have hAX : x ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel hx <
        F.boundaryLabel
          ((κ.repair a b c d v hsq).pathMatch_mem hx) ∧
       chainDir (o.portFlip hpf) x = true) := by
    rw [mem_antiLowSet_transport hsq (o.portFlip hpf) hflip]
    constructor
    · rintro ⟨hx', hint', hlt, hdir⟩
      exact ⟨hlt, hdir⟩
    · rintro ⟨hlt, hdir⟩
      exact ⟨hx, hxint, hlt, hdir⟩
  have hAY : (κ.repair a b c d v hsq).pathMatch x hx ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel
          ((κ.repair a b c d v hsq).pathMatch_mem hx) <
        F.boundaryLabel hx ∧
       chainDir (o.portFlip hpf)
         ((κ.repair a b c d v hsq).pathMatch x hx) = true) := by
    rw [mem_antiLowSet_transport hsq (o.portFlip hpf) hflip]
    constructor
    · rintro ⟨hy', hint', hlt, hdir⟩
      refine ⟨?_, hdir⟩
      have hlt' : F.boundaryLabel hy <
          F.boundaryLabel
            ((κ.repair a b c d v hsq).pathMatch_mem hy) := hlt
      rwa [boundaryLabel_congr
        ((κ.repair a b c d v hsq).pathMatch_mem hy) hx hinv]
        at hlt'
    · rintro ⟨hlt, hdir⟩
      refine ⟨hy, hyint, ?_, hdir⟩
      rwa [boundaryLabel_congr
        ((κ.repair a b c d v hsq).pathMatch_mem hy) hx hinv]
  -- new-chord rigidity at the preserved directions
  have hrig : chainDir (o.portFlip hpf)
      ((κ.repair a b c d v hsq).pathMatch x hx) =
      !chainDir (o.portFlip hpf) x := by
    have h := chainDir_pathMatch
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) hx hxint
    rw [chainDir_transportRepair, chainDir_transportRepair] at h
    exact h
  -- the canonical direction formula at the source
  have hcanx : chainDir o x = true ↔
      F.boundaryLabel (κ.pathMatch_mem hx) < F.boundaryLabel hx :=
    chainDir_true_iff_high hc hx hxint
  -- ═══════ STAGE 2: THE ANTI DISJUNCTION AS `new-high ⊕ flipped-dir` ═══════
  have h1 : (x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq
          (o.portFlip hpf) hflip) ∨
      (κ.repair a b c d v hsq).pathMatch x hx ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq
          (o.portFlip hpf) hflip)) ↔
      ((F.boundaryLabel
          ((κ.repair a b c d v hsq).pathMatch_mem hx) <
        F.boundaryLabel hx) ≠
        (chainDir (o.portFlip hpf) x = true)) := by
    rw [hAX, hAY, hrig]
    cases hdd : chainDir (o.portFlip hpf) x
    · rw [Bool.not_false]
      constructor
      · rintro (⟨-, hcon⟩ | ⟨hplt, -⟩)
        · exact absurd hcon Bool.false_ne_true
        · exact prop_ne_of_left hplt Bool.false_ne_true
      · intro h
        rcases prop_ne_cases h with ⟨hplt, -⟩ | ⟨-, hcon⟩
        · exact Or.inr ⟨hplt, rfl⟩
        · exact absurd hcon Bool.false_ne_true
    · rw [Bool.not_true]
      constructor
      · rintro (⟨hnlt, -⟩ | ⟨-, hcon⟩)
        · exact prop_ne_of_right
            (fun hplt => lt_asymm hnlt hplt) rfl
        · exact absurd hcon Bool.false_ne_true
      · intro h
        rcases prop_ne_cases h with ⟨-, hcon⟩ | ⟨hnplt, -⟩
        · exact absurd rfl hcon
        · exact Or.inl
            ⟨(lt_or_gt_of_ne hlabne).resolve_right hnplt, rfl⟩
  -- ═══════ STAGE 3: THE FLIPPED DIRECTION AS `old-high ⊕ toggle` ═══════
  have h2 : (chainDir (o.portFlip hpf) x = true) ↔
      ((F.boundaryLabel (κ.pathMatch_mem hx) <
        F.boundaryLabel hx) ≠ (W.pairing x ∈ S)) := by
    by_cases hTx : W.pairing x ∈ S
    · rw [chainDir_portFlip_of_mem o hpf hTx]
      cases hdc : chainDir o x
      · rw [Bool.not_false]
        have hnolt : ¬ (F.boundaryLabel (κ.pathMatch_mem hx) <
            F.boundaryLabel hx) := fun h =>
          Bool.false_ne_true (((hcanx.mpr h).symm.trans hdc).symm)
        exact iff_of_true rfl (prop_ne_of_right hnolt hTx)
      · rw [Bool.not_true]
        have holt := hcanx.mp hdc
        refine iff_of_false Bool.false_ne_true ?_
        intro h
        rcases prop_ne_cases h with ⟨-, hnT⟩ | ⟨hnolt, -⟩
        · exact hnT hTx
        · exact hnolt holt
    · rw [chainDir_portFlip_of_notMem o hpf hTx]
      constructor
      · intro hd
        exact prop_ne_of_left (hcanx.mp hd) hTx
      · intro h
        rcases prop_ne_cases h with ⟨holt, -⟩ | ⟨-, hT⟩
        · exact hcanx.mpr holt
        · exact absurd hT hTx
  -- ═══════ ASSEMBLY: ROTATE THE THREE-WAY XOR ═══════
  rw [h1, h2,
    mem_highSet_iff_lt (κ := κ.repair a b c d v hsq) hx hxint,
    mem_highSet_iff_lt (κ := κ) hx hxint]
  exact prop_xor_rotate

/-- **The non-separated per-step status identification**: for the
anchored transported frame of a non-separated step from a canonical
source — flip the anchor chain of `β₂` (the `c`-chain, realized as
the ported flip set `S` with the chord's two end labels `iβ`, `iγ`),
then transport across the repair — the fold of the anchor pair
`(iβ, iγ)` with a full pairwise-disjoint anti-low list of the
transported frame is exactly the set of labels whose high-status
differs between the repaired and the source systems.  The anchor
pair is `β₂`'s chord in the *source* system; the list pairs are
anti-low chords of the *repaired* system at the transported
frame. -/
theorem nonsep_labels_eq_statusChange
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    {S : Finset W.Flag} {p₁ p₂ : W.Flag} {iβ iγ : α}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hc : PathCanonical o)
    (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    (hflip : (o.portFlip hpf).isOut c = !(o.portFlip hpf).isOut a)
    {β₂ : W.Flag} (hβ₂ : β₂ ∈ F.boundaryFlags)
    (hint₂ : W.pairing β₂ ∈ F.internalFlags)
    (honS : ∀ f ∈ S, OnBoundaryChain κ β₂ f)
    (hSon : ∀ f ∈ F.internalFlags,
      OnBoundaryChain κ β₂ f → f ∈ S)
    (hlabβ : F.boundaryLabel hβ₂ = iβ)
    (hlabγ : F.boundaryLabel (κ.pathMatch_mem hβ₂) = iγ)
    {L : List (α × α)}
    (hall : ∀ p ∈ L, AntiLowPair
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) p)
    (hdisj : L.Pairwise PairDisjoint)
    (hlen : L.length = (antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip)).card)
    {i : α} :
    (i ∈ pairFold ((iβ, iγ) :: L)) ↔
      ((i ∈ highSet (κ.repair a b c d v hsq)) ≠
        (i ∈ highSet κ)) := by
  have hps : i ∈ pairSet (iβ, iγ) ↔ (i = iβ ∨ i = iγ) :=
    mem_pairSet
  rw [pairFold_cons, mem_symmU, hps,
    mem_pairFold_antiLow hall hdisj hlen]
  -- ═══════ IS THE LABEL A PARTICIPATING END? ═══════
  -- If it is, the anchor toggle and the chord rigidity combine by
  -- a three-term XOR; if not, both sides are false.
  by_cases hpart : ∃ (x : W.Flag) (hx : x ∈ F.boundaryFlags),
      W.pairing x ∈ F.internalFlags ∧ F.boundaryLabel hx = i
  · -- the label of a participating end: the XOR algebra
    obtain ⟨x, hx, hxint, hlabx⟩ := hpart
    subst hlabx
    have hE1 : (F.boundaryLabel hx = iβ ∨
        F.boundaryLabel hx = iγ) ↔ W.pairing x ∈ S := by
      rw [pairing_mem_flipSet_iff hpf hβ₂ hint₂ honS hSon hx
        hxint]
      constructor
      · rintro (h | h)
        · exact Or.inl (boundaryLabel_inj hx hβ₂
            (h.trans hlabβ.symm))
        · exact Or.inr (boundaryLabel_inj hx
            (κ.pathMatch_mem hβ₂) (h.trans hlabγ.symm))
      · rintro (h | h)
        · exact Or.inl ((boundaryLabel_congr hx hβ₂ h).trans
            hlabβ)
        · exact Or.inr ((boundaryLabel_congr hx
            (κ.pathMatch_mem hβ₂) h).trans hlabγ)
    have hF : (∃ (β : W.Flag) (hβ : β ∈ F.boundaryFlags),
        β ∈ antiLowSet
          (RelTransitionSystem.Orientation.transportRepair hsq
            (o.portFlip hpf) hflip) ∧
        (F.boundaryLabel hx = F.boundaryLabel hβ ∨
         F.boundaryLabel hx = F.boundaryLabel
           ((κ.repair a b c d v hsq).pathMatch_mem hβ))) ↔
        (x ∈ antiLowSet
            (RelTransitionSystem.Orientation.transportRepair hsq
              (o.portFlip hpf) hflip) ∨
          (κ.repair a b c d v hsq).pathMatch x hx ∈ antiLowSet
            (RelTransitionSystem.Orientation.transportRepair hsq
              (o.portFlip hpf) hflip)) := by
      constructor
      · rintro ⟨β, hβ, hmem, hlab | hlab⟩
        · refine Or.inl ?_
          rw [boundaryLabel_inj hx hβ hlab]
          exact hmem
        · refine Or.inr ?_
          have hxβ : x =
              (κ.repair a b c d v hsq).pathMatch β hβ :=
            boundaryLabel_inj hx
              ((κ.repair a b c d v hsq).pathMatch_mem hβ) hlab
          have hpmx : (κ.repair a b c d v hsq).pathMatch x hx =
              β :=
            ((κ.repair a b c d v hsq).pathMatch_congr hxβ hx
              ((κ.repair a b c d v hsq).pathMatch_mem hβ)).trans
              ((κ.repair a b c d v hsq).pathMatch_invol hβ)
          rw [hpmx]
          exact hmem
      · rintro (hmem | hmem)
        · exact ⟨x, hx, hmem, Or.inl rfl⟩
        · exact ⟨(κ.repair a b c d v hsq).pathMatch x hx,
            (κ.repair a b c d v hsq).pathMatch_mem hx, hmem,
            Or.inr (boundaryLabel_congr hx
              ((κ.repair a b c d v hsq).pathMatch_mem
                ((κ.repair a b c d v hsq).pathMatch_mem hx))
              ((κ.repair a b c d v hsq).pathMatch_invol
                hx).symm)⟩
    have hFC := hF.trans
      (anti_ends_iff_toggle_xor_status hsq hc hpf hflip hx hxint)
    rw [hFC, hE1, ← prop_ne_iff]
    exact prop_xor_cancel
  · -- a non-participating label: both sides are false
    constructor
    · rintro (⟨hor, -⟩ | ⟨⟨β, hβ, hmem, hlab⟩, -⟩)
      · exfalso
        rcases hor with rfl | rfl
        · exact hpart ⟨β₂, hβ₂, hint₂, hlabβ⟩
        · exact hpart ⟨κ.pathMatch β₂ hβ₂, κ.pathMatch_mem hβ₂,
            pathMatch_pairing_internal (κ := κ) hβ₂ hint₂,
            hlabγ⟩
      · exfalso
        obtain ⟨hβ', hintβ, -, -⟩ := mem_antiLowSet.mp hmem
        rcases hlab with rfl | rfl
        · exact hpart ⟨β, hβ, hintβ, rfl⟩
        · exact hpart ⟨(κ.repair a b c d v hsq).pathMatch β hβ,
            (κ.repair a b c d v hsq).pathMatch_mem hβ,
            pathMatch_pairing_internal
              (κ := κ.repair a b c d v hsq) hβ hintβ, rfl⟩
    · intro hch
      exfalso
      rcases prop_ne_cases hch with ⟨hnew, -⟩ | ⟨-, hold⟩
      · obtain ⟨δ, hδ, hint, -, hlabδ⟩ := mem_highSet.mp hnew
        exact hpart ⟨δ, hδ, hint, hlabδ⟩
      · obtain ⟨δ, hδ, hint, -, hlabδ⟩ := mem_highSet.mp hold
        exact hpart ⟨δ, hδ, hint, hlabδ⟩

end StepStatusNonsep

end EdgeSubset

end RS
