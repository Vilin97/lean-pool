/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StepFrame
import LeanPool.RegtsSevenster.RS.Novel.Skein.LabelChords

/-!
# The high-status set of a pairing

The labels whose boundary end is the high end of its chord: the
potential function of the canonical route's state relabels.  On
the canonical route the chain direction at every participating end
equals its high-status, so the accumulated relabel set is the
high-status difference of the endpoint pairings — empty exactly
when the pairing returns.
-/

namespace RS



variable {α : Type}

namespace EdgeSubset

open Classical in
/-- The labels whose participating boundary end is the high end of
its chord. -/
noncomputable def highSet [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) :
    Finset α :=
  (F.boundaryFlags.attach.filter (fun b =>
    W.pairing b.val ∈ F.internalFlags ∧
    F.boundaryLabel (κ.pathMatch_mem b.prop) <
      F.boundaryLabel b.prop)).image
    (fun b => F.boundaryLabel b.prop)

/-- Membership in the high-status set: a label that is the high end
of its chord. -/
theorem mem_highSet [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {i : α} :
    i ∈ highSet κ ↔
      ∃ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        W.pairing δ ∈ F.internalFlags ∧
        F.boundaryLabel (κ.pathMatch_mem hδ) <
          F.boundaryLabel hδ ∧
        F.boundaryLabel hδ = i := by
  unfold highSet
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨δ, hδ⟩, hmem, rfl⟩
    obtain ⟨-, hint, hlt⟩ := Finset.mem_filter.mp hmem
    exact ⟨δ, hδ, hint, hlt, rfl⟩
  · rintro ⟨δ, hδ, hint, hlt, rfl⟩
    exact ⟨⟨δ, hδ⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_attach _ _, hint, hlt⟩, rfl⟩

/-- The high-status set only sees the pairing. -/
theorem highSet_of_samePairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (h : SamePairing κ κ') : highSet κ = highSet κ' := by
  unfold highSet
  refine congrArg _ (Finset.filter_congr ?_)
  rintro ⟨δ, hδ⟩ -
  rw [boundaryLabel_congr (κ.pathMatch_mem hδ)
    (κ'.pathMatch_mem hδ) (h δ hδ)]

/-- Membership at a given end's label reduces to the label
comparison at that end. -/
theorem mem_highSet_iff_lt [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {δ : W.Flag} (hδ : δ ∈ F.boundaryFlags)
    (hint : W.pairing δ ∈ F.internalFlags) :
    F.boundaryLabel hδ ∈ highSet κ ↔
      F.boundaryLabel (κ.pathMatch_mem hδ) <
        F.boundaryLabel hδ := by
  rw [mem_highSet]
  constructor
  · rintro ⟨γ, hγ, hint', hlt, heq⟩
    have hδγ : δ = γ := boundaryLabel_inj hδ hγ heq.symm
    subst hδγ
    exact hlt
  · intro h
    exact ⟨δ, hδ, hint, h, rfl⟩

/-- **Untouched ends keep their status** across a repair. -/
theorem mem_highSet_repair_untouched
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    {e₁ e₂ : W.Flag} (he₁ : e₁ ∈ F.boundaryFlags)
    (he₂ : e₂ ∈ F.boundaryFlags)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ e₁ → δ ≠ e₂ → δ ≠ κ.pathMatch e₁ he₁ →
      δ ≠ κ.pathMatch e₂ he₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ)
    {δ : W.Flag} (hδ : δ ∈ F.boundaryFlags)
    (hint : W.pairing δ ∈ F.internalFlags)
    (h1 : δ ≠ e₁) (h2 : δ ≠ e₂) (h3 : δ ≠ κ.pathMatch e₁ he₁)
    (h4 : δ ≠ κ.pathMatch e₂ he₂) :
    (F.boundaryLabel hδ ∈ highSet (κ.repair a b c d v hsq) ↔
      F.boundaryLabel hδ ∈ highSet κ) := by
  rw [mem_highSet_iff_lt hδ hint, mem_highSet_iff_lt hδ hint,
    boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hδ)
      (κ.pathMatch_mem hδ) (hout δ hδ h1 h2 h3 h4)]

/-- **The re-paired end's status** is the comparison against its
new partner. -/
theorem mem_highSet_repair_end
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    {x y : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hy : y ∈ F.boundaryFlags)
    (hint : W.pairing x ∈ F.internalFlags)
    (hnew : (κ.repair a b c d v hsq).pathMatch x hx = y) :
    (F.boundaryLabel hx ∈ highSet (κ.repair a b c d v hsq) ↔
      F.boundaryLabel hy < F.boundaryLabel hx) := by
  rw [mem_highSet_iff_lt hx hint,
    boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hx) hy hnew]

end EdgeSubset

end RS
