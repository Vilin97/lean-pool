/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonicalFrame
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingSwap

/-!
# The frame across a separated two-path step

The separated transport keeps `isOut` verbatim, so the chain
direction observable is preserved pointwise; canonicality after
the step is therefore measured by the *new* chords' low ends
against the *old* directions — pure label combinatorics.  The new
pairing's rigidity forces the re-paired ends to carry opposite
directions, a constraint on the old frame derived from the new
system.
-/

namespace RS

open scoped Classical

variable {α : Type}

namespace EdgeSubset

/-- The separated transport preserves the chain direction at every
flag. -/
theorem chainDir_transportRepair
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a : W.Flag} {b : W.Flag} {c : W.Flag} {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a)
    (δ : W.Flag) :
    chainDir (RelTransitionSystem.Orientation.transportRepair hsq
        o hflip) δ = chainDir o δ := rfl

/-- **The re-paired ends carry opposite directions**: the new
chord's rigidity, read back through the preserved directions, is a
constraint on the old frame. -/
theorem swap_dirs_opposite
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a : W.Flag} {b : W.Flag} {c : W.Flag} {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (hcross : (κ.repair a b c d v hsq).pathMatch e₁ he₁ = e₂)
    (hint : W.pairing e₁ ∈ F.internalFlags) :
    chainDir o e₂ = !chainDir o e₁ := by
  have h := chainDir_pathMatch
    (RelTransitionSystem.Orientation.transportRepair hsq o hflip)
    he₁ hint
  rw [hcross] at h
  rw [chainDir_transportRepair, chainDir_transportRepair] at h
  exact h

/-- Membership in the transported frame's anti-canonical set:
directions are the old ones, labels are the new chords'. -/
theorem mem_antiLowSet_transport
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a)
    {x : W.Flag} :
    x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) ↔
      ∃ hx : x ∈ F.boundaryFlags,
        W.pairing x ∈ F.internalFlags ∧
        F.boundaryLabel hx <
          F.boundaryLabel
            ((κ.repair a b c d v hsq).pathMatch_mem hx) ∧
        chainDir o x = true := by
  rw [mem_antiLowSet]
  exact exists_congr fun hx => and_congr_right fun _ =>
    and_congr_right fun _ => by
      rw [chainDir_transportRepair]

/-- **Untouched chains keep their anti-canonicality** across the
transported step: off the four re-paired ends both the label
comparison and the direction are unchanged. -/
theorem mem_antiLowSet_transport_untouched
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
      δ ≠ κ.pathMatch e₂ he₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ)
    {x : W.Flag} (hx1 : x ≠ e₁) (hx2 : x ≠ e₂)
    (hx3 : x ≠ κ.pathMatch e₁ he₁) (hx4 : x ≠ κ.pathMatch e₂ he₂) :
    (x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) ↔ x ∈ antiLowSet o) := by
  rw [mem_antiLowSet_transport hsq o hflip, mem_antiLowSet]
  constructor
  · rintro ⟨hx, hint, hlt, hdir⟩
    refine ⟨hx, hint, ?_, hdir⟩
    rwa [boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hx)
      (κ.pathMatch_mem hx) (hout x hx hx1 hx2 hx3 hx4)] at hlt
  · rintro ⟨hx, hint, hlt, hdir⟩
    refine ⟨hx, hint, ?_, hdir⟩
    rwa [boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hx)
      (κ.pathMatch_mem hx) (hout x hx hx1 hx2 hx3 hx4)]

/-- **The canonical direction formula**: on a participating chain a
canonical frame points `true` exactly at the high-labelled end. -/
theorem chainDir_true_iff_high
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation}
    (hc : PathCanonical o) {x : W.Flag}
    (hx : x ∈ F.boundaryFlags)
    (hint : W.pairing x ∈ F.internalFlags) :
    chainDir o x = true ↔
      F.boundaryLabel (κ.pathMatch_mem hx) < F.boundaryLabel hx := by
  have hne : F.boundaryLabel hx ≠
      F.boundaryLabel (κ.pathMatch_mem hx) := fun h =>
    κ.pathMatch_ne_self hx
      (boundaryLabel_inj (κ.pathMatch_mem hx) hx h.symm)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- x is the low end: direction false
    have h0 := (pathCanonical_iff_chainDir o).mp hc x hx hint hlt
    constructor
    · intro h1
      exact absurd (h0.symm.trans h1) (by decide)
    · intro h1
      exact absurd h1 (not_lt_of_gt hlt)
  · -- x is the high end: the far end is low, rigidity flips
    have hπmem := κ.pathMatch_mem hx
    have hπint := pathMatch_pairing_internal (κ := κ) hx hint
    have hππ : κ.pathMatch (κ.pathMatch x hx) hπmem = x :=
      κ.pathMatch_invol hx
    have hlow : F.boundaryLabel hπmem <
        F.boundaryLabel (κ.pathMatch_mem hπmem) := by
      rw [boundaryLabel_congr (κ.pathMatch_mem hπmem) hx hππ]
      exact hgt
    have h0 := (pathCanonical_iff_chainDir o).mp hc _ hπmem hπint
      hlow
    have h1 := chainDir_pathMatch o hx hint
    rw [h0] at h1
    constructor
    · intro _
      exact hgt
    · intro _
      have h2 : chainDir o x = true := by
        have h3 := congrArg (fun z => !z) h1
        simpa using h3.symm
      exact h2

/-- **The four-end evaluation**: from a canonical frame, an end of
a re-paired chord is anti-canonical after the transported step
exactly when it is low in its new chord but was high in its old
one.  (Instantiate at the four swap ends with the new partners
from `pathMatch_repair_swap`.) -/
theorem mem_antiLowSet_transport_of_canonical
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {x y : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hy : y ∈ F.boundaryFlags)
    (hint : W.pairing x ∈ F.internalFlags)
    (hnew : (κ.repair a b c d v hsq).pathMatch x hx = y) :
    (x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) ↔
      (F.boundaryLabel hx < F.boundaryLabel hy ∧
        F.boundaryLabel (κ.pathMatch_mem hx) <
          F.boundaryLabel hx)) := by
  rw [mem_antiLowSet_transport hsq o hflip]
  have hlab : F.boundaryLabel
      ((κ.repair a b c d v hsq).pathMatch_mem hx) =
      F.boundaryLabel hy :=
    boundaryLabel_congr _ hy hnew
  constructor
  · rintro ⟨hx', hint', hlt, hdir⟩
    exact ⟨hlab ▸ hlt,
      (chainDir_true_iff_high hc hx hint).mp hdir⟩
  · rintro ⟨hlt, hhigh⟩
    exact ⟨hx, hint, hlab.symm ▸ hlt,
      (chainDir_true_iff_high hc hx hint).mpr hhigh⟩

/-- **The transported anti-canonical set lives on the four
re-paired ends**: from a canonical source frame, every other chain
stays canonical. -/
theorem antiLowSet_transport_subset
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
      δ ≠ κ.pathMatch e₂ he₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ) :
    antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) ⊆
      {e₁, e₂, κ.pathMatch e₁ he₁, κ.pathMatch e₂ he₂} := by
  intro x hx
  by_contra hmem
  have h1 : x ≠ e₁ := fun h => hmem (by
    rw [h]
    exact Finset.mem_insert_self _ _)
  have h2 : x ≠ e₂ := fun h => hmem (by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h3 : x ≠ κ.pathMatch e₁ he₁ := fun h => hmem (by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
  have h4 : x ≠ κ.pathMatch e₂ he₂ := fun h => hmem (by
    rw [h]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
  have hx' := (mem_antiLowSet_transport_untouched hsq o hflip
    he₁ he₂ hout h1 h2 h3 h4).mp hx
  rw [pathCanonical_iff_antiLowSet_empty] at hc
  rw [hc] at hx'
  exact Finset.notMem_empty x hx'

/-- The low end of the `(e₁, e₂)` chord, as a flag. -/
noncomputable def newLow [LinearOrder α] {W : Fragment α}
    (F : EdgeSubset W) {e₁ : W.Flag}
    (he₁ : e₁ ∈ F.boundaryFlags) (e₂ : W.Flag)
    (he₂ : e₂ ∈ F.boundaryFlags) : W.Flag :=
  if F.boundaryLabel he₁ < F.boundaryLabel he₂ then e₁ else e₂

/-- **The transported anti set, exactly**: the two new chords'
low ends, each present exactly when it was high in its old
chord. -/
theorem antiLowSet_transport_eq
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hne : e₁ ≠ e₂) (hPne : κ.pathMatch e₁ he₁ ≠ e₂)
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
    (hintP₂ : W.pairing (κ.pathMatch e₂ he₂) ∈ F.internalFlags) :
    antiLowSet (RelTransitionSystem.Orientation.transportRepair
        hsq o hflip) =
      (if (if F.boundaryLabel he₁ < F.boundaryLabel he₂ then
            F.boundaryLabel (κ.pathMatch_mem he₁) <
              F.boundaryLabel he₁
          else
            F.boundaryLabel (κ.pathMatch_mem he₂) <
              F.boundaryLabel he₂) then
        {newLow F he₁ e₂ he₂} else ∅) ∪
      (if (if F.boundaryLabel (κ.pathMatch_mem he₁) <
            F.boundaryLabel (κ.pathMatch_mem he₂) then
            F.boundaryLabel he₁ <
              F.boundaryLabel (κ.pathMatch_mem he₁)
          else
            F.boundaryLabel he₂ <
              F.boundaryLabel (κ.pathMatch_mem he₂)) then
        {newLow F (κ.pathMatch_mem he₁) (κ.pathMatch e₂ he₂)
          (κ.pathMatch_mem he₂)} else ∅) := by
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
  have hP₁P₂ : κ.pathMatch e₁ he₁ ≠ κ.pathMatch e₂ he₂ := by
    intro h
    apply hne
    calc e₁ = κ.pathMatch (κ.pathMatch e₁ he₁)
          (κ.pathMatch_mem he₁) := (κ.pathMatch_invol he₁).symm
      _ = κ.pathMatch (κ.pathMatch e₂ he₂)
          (κ.pathMatch_mem he₂) :=
        κ.pathMatch_congr h (κ.pathMatch_mem he₁)
          (κ.pathMatch_mem he₂)
      _ = e₂ := κ.pathMatch_invol he₂
  have hL12 : F.boundaryLabel he₁ ≠ F.boundaryLabel he₂ :=
    fun h => hne (boundaryLabel_inj he₁ he₂ h)
  have hLP : F.boundaryLabel (κ.pathMatch_mem he₁) ≠
      F.boundaryLabel (κ.pathMatch_mem he₂) :=
    fun h => hP₁P₂ (boundaryLabel_inj (κ.pathMatch_mem he₁)
      (κ.pathMatch_mem he₂) h)
  -- ═══════ THE FOUR RE-PAIRED ENDS ═══════
  -- Above: they are four distinct flags with four distinct labels.
  -- Below: which of them the transported frame calls anti-canonical.
  have hm₁ := mem_antiLowSet_transport_of_canonical hsq hflip hc
    he₁ he₂ hint₁ hcross
  have hm₂ := mem_antiLowSet_transport_of_canonical hsq hflip hc
    he₂ he₁ hint₂ hcross₂
  have hm₃ := mem_antiLowSet_transport_of_canonical hsq hflip hc
    (κ.pathMatch_mem he₁) (κ.pathMatch_mem he₂) hintP₁ hfar
  have hm₄ := mem_antiLowSet_transport_of_canonical hsq hflip hc
    (κ.pathMatch_mem he₂) (κ.pathMatch_mem he₁) hintP₂ hfar₂
  have hππ₁ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem he₁)) =
      F.boundaryLabel he₁ :=
    boundaryLabel_congr _ he₁ (κ.pathMatch_invol he₁)
  have hππ₂ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem he₂)) =
      F.boundaryLabel he₂ :=
    boundaryLabel_congr _ he₂ (κ.pathMatch_invol he₂)
  rw [hππ₁] at hm₃
  rw [hππ₂] at hm₄
  apply Finset.ext
  -- ═══════ THE TWO SETS AGREE ELEMENTWISE ═══════
  intro x
  rw [Finset.mem_union]
  constructor
  · intro hx
    have hx4 := antiLowSet_transport_subset hsq hflip hc he₁ he₂
      hout hx
    rcases Finset.mem_insert.mp hx4 with rfl | hx4b
    · obtain ⟨hlt, hhigh⟩ := hm₁.mp hx
      left
      rw [if_pos (by rw [if_pos hlt]; exact hhigh)]
      rw [Finset.mem_singleton, newLow, if_pos hlt]
    · rcases Finset.mem_insert.mp hx4b with rfl | hx4c
      · obtain ⟨hlt, hhigh⟩ := hm₂.mp hx
        left
        have hnlt : ¬ F.boundaryLabel he₁ < F.boundaryLabel he₂ :=
          fun h => lt_asymm h hlt
        rw [if_pos (by rw [if_neg hnlt]; exact hhigh)]
        rw [Finset.mem_singleton, newLow, if_neg hnlt]
      · rcases Finset.mem_insert.mp hx4c with rfl | hx4d
        · obtain ⟨hlt, hhigh⟩ := hm₃.mp hx
          right
          rw [if_pos (by rw [if_pos hlt]; exact hhigh)]
          rw [Finset.mem_singleton, newLow, if_pos hlt]
        · rw [Finset.mem_singleton] at hx4d
          subst hx4d
          obtain ⟨hlt, hhigh⟩ := hm₄.mp hx
          right
          have hnlt : ¬ F.boundaryLabel (κ.pathMatch_mem he₁) <
              F.boundaryLabel (κ.pathMatch_mem he₂) :=
            fun h => lt_asymm h hlt
          rw [if_pos (by rw [if_neg hnlt]; exact hhigh)]
          rw [Finset.mem_singleton, newLow, if_neg hnlt]
  · intro hx
    rcases hx with hx | hx
    · by_cases hcond : (if F.boundaryLabel he₁ <
          F.boundaryLabel he₂ then
          F.boundaryLabel (κ.pathMatch_mem he₁) <
            F.boundaryLabel he₁
        else
          F.boundaryLabel (κ.pathMatch_mem he₂) <
            F.boundaryLabel he₂)
      · rw [if_pos hcond, Finset.mem_singleton] at hx
        subst hx
        unfold newLow
        by_cases hlt : F.boundaryLabel he₁ < F.boundaryLabel he₂
        · rw [if_pos hlt]
          rw [if_pos hlt] at hcond
          exact hm₁.mpr ⟨hlt, hcond⟩
        · rw [if_neg hlt]
          rw [if_neg hlt] at hcond
          have hlt2 : F.boundaryLabel he₂ <
              F.boundaryLabel he₁ :=
            lt_of_le_of_ne (not_lt.mp hlt)
              (fun h => hL12 h.symm)
          exact hm₂.mpr ⟨hlt2, hcond⟩
      · rw [if_neg hcond] at hx
        exact absurd hx (Finset.notMem_empty _)
    · by_cases hcond : (if F.boundaryLabel
          (κ.pathMatch_mem he₁) <
          F.boundaryLabel (κ.pathMatch_mem he₂) then
          F.boundaryLabel he₁ <
            F.boundaryLabel (κ.pathMatch_mem he₁)
        else
          F.boundaryLabel he₂ <
            F.boundaryLabel (κ.pathMatch_mem he₂))
      · rw [if_pos hcond, Finset.mem_singleton] at hx
        subst hx
        unfold newLow
        by_cases hlt : F.boundaryLabel (κ.pathMatch_mem he₁) <
            F.boundaryLabel (κ.pathMatch_mem he₂)
        · rw [if_pos hlt]
          rw [if_pos hlt] at hcond
          exact hm₃.mpr ⟨hlt, hcond⟩
        · rw [if_neg hlt]
          rw [if_neg hlt] at hcond
          have hlt2 : F.boundaryLabel (κ.pathMatch_mem he₂) <
              F.boundaryLabel (κ.pathMatch_mem he₁) :=
            lt_of_le_of_ne (not_lt.mp hlt)
              (fun h => hLP h.symm)
          exact hm₄.mpr ⟨hlt2, hcond⟩
      · rw [if_neg hcond] at hx
        exact absurd hx (Finset.notMem_empty _)

/-- **The flip count of a separated canonical step**: the four-label
indicator sum — the exact left side of the parity identity. -/
theorem antiLowSet_transport_card
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hflip : o.isOut c = !o.isOut a) (hc : PathCanonical o)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hne : e₁ ≠ e₂) (hPne : κ.pathMatch e₁ he₁ ≠ e₂)
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
    (hintP₂ : W.pairing (κ.pathMatch e₂ he₂) ∈ F.internalFlags) :
    (antiLowSet (RelTransitionSystem.Orientation.transportRepair
        hsq o hflip)).card =
      (if (if F.boundaryLabel he₁ < F.boundaryLabel he₂ then
            F.boundaryLabel (κ.pathMatch_mem he₁) <
              F.boundaryLabel he₁
          else
            F.boundaryLabel (κ.pathMatch_mem he₂) <
              F.boundaryLabel he₂) then 1 else 0) +
      (if (if F.boundaryLabel (κ.pathMatch_mem he₁) <
            F.boundaryLabel (κ.pathMatch_mem he₂) then
            F.boundaryLabel he₁ <
              F.boundaryLabel (κ.pathMatch_mem he₁)
          else
            F.boundaryLabel he₂ <
              F.boundaryLabel (κ.pathMatch_mem he₂))
        then 1 else 0) := by
  rw [antiLowSet_transport_eq hsq hflip hc he₁ he₂ hne hPne
    hcross hfar hout hint₁ hint₂ hintP₁ hintP₂]
  have hdisj : ∀ z₁ z₂ : W.Flag,
      (z₁ = e₁ ∨ z₁ = e₂) →
      (z₂ = κ.pathMatch e₁ he₁ ∨ z₂ = κ.pathMatch e₂ he₂) →
      z₁ ≠ z₂ := by
    rintro z₁ z₂ (rfl | rfl) (rfl | rfl)
    · exact fun h => κ.pathMatch_ne_self he₁ h.symm
    · intro h
      apply hPne
      exact ((κ.pathMatch_congr h he₁
        (κ.pathMatch_mem he₂)).trans (κ.pathMatch_invol he₂))
    · exact fun h => hPne h.symm
    · exact fun h => κ.pathMatch_ne_self he₂ h.symm
  have hz : newLow F he₁ e₂ he₂ ≠
      newLow F (κ.pathMatch_mem he₁) (κ.pathMatch e₂ he₂)
        (κ.pathMatch_mem he₂) := by
    apply hdisj
    · unfold newLow
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    · unfold newLow
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
  split_ifs <;>
    first
      | (rw [Finset.card_union_of_disjoint (by
            rw [Finset.disjoint_singleton]
            exact hz)]
         rfl)
      | (rw [Finset.union_empty]
         rfl)
      | (rw [Finset.empty_union]
         rfl)

/-- Canonicality and the summand cross a `MatchEq` unchanged (the
unsigned endpoint transfer). -/
theorem matchEq_canonical_transfer
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂)
    {o : κ₁.Orientation} (hc : PathCanonical o) :
    ∃ o' : κ₂.Orientation, PathCanonical o' ∧
      F.throughSummand hM st hbnd o' κ₂.openCircuitCount =
        F.throughSummand hM st hbnd o κ₁.openCircuitCount := by
  refine ⟨RelTransitionSystem.Orientation.ofMatchEq heq o, ?_, ?_⟩
  · intro i j hb hint hpm hij
    exact hc i j hb hint (by
      rw [← pathMatch_matchEq heq (δ := W.boundaryFlag i) hb]
      exact hpm) hij
  · rw [openCircuitCount_matchEq heq]
    exact throughSummand_ofMatchEq hM st hbnd heq o
      κ₁.openCircuitCount

end EdgeSubset

/-- The paired step without the chord signs: within a block the
pairing returns, so the two path signs agree and cancel. -/
def PairedLedgerUnsigned : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ₁ κ₂ : F.RelTransitionSystem),
    EdgeSubset.PairedStep κ₁ κ₂ →
    ∀ (o₁ : κ₁.Orientation), EdgeSubset.PathCanonical o₁ →
    ∃ (o₂ : κ₂.Orientation), EdgeSubset.PathCanonical o₂ ∧
      F.throughSummand hM st hbnd o₂ κ₂.openCircuitCount =
        F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount

namespace EdgeSubset

/-- The signed and unsigned paired steps coincide. -/
theorem pairedLedger_iff_unsigned :
    EdgeSubset.PairedLedger ↔ PairedLedgerUnsigned := by
  constructor
  · intro H α _ W F k ℓ hM st hbnd κ₁ κ₂ hps o₁ hc₁
    obtain ⟨o₂, hc₂, hval⟩ := H hM st hbnd κ₁ κ₂ hps o₁ hc₁
    have hpsign : pathSign κ₁ = pathSign κ₂ :=
      pathSign_of_samePairing hps.2
    have hnz : pathSign κ₂ ≠ 0 := by
      unfold pathSign
      exact pow_ne_zero _ (by norm_num)
    refine ⟨o₂, hc₂, ?_⟩
    rw [hpsign] at hval
    exact mul_left_cancel₀ hnz hval
  · intro H α _ W F k ℓ hM st hbnd κ₁ κ₂ hps o₁ hc₁
    obtain ⟨o₂, hc₂, hval⟩ := H hM st hbnd κ₁ κ₂ hps o₁ hc₁
    refine ⟨o₂, hc₂, ?_⟩
    rw [hval, pathSign_of_samePairing hps.2]

end EdgeSubset

end RS
