/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingValue
import LeanPool.RegtsSevenster.RS.Novel.Skein.StepLedger

/-!
# The ledgers in value form

The pairing-preserving ledgers restated for the pairing-resolved
signed value: existence of a matching canonical orientation plus
equality of signed summands is exactly preservation of
`signedValueAt` together with transfer of canonical-orientation
existence.  The single-step disjunct is a theorem
(`stepLedger_single`), so the move ledger in value form reduces to
the paired step in value form.
-/

namespace RS



/-- **The paired step, value form**: across a π-returning
repair block, canonical-orientation existence transfers and the
pairing-resolved signed value is preserved. -/
def PairedValueLedger : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ₁ κ₂ : F.RelTransitionSystem),
    EdgeSubset.PairedStep κ₁ κ₂ →
    Nonempty {o : κ₁.Orientation // EdgeSubset.PathCanonical o} →
    Nonempty {o : κ₂.Orientation // EdgeSubset.PathCanonical o} ∧
      F.signedValueAt hM st hbnd κ₁ = F.signedValueAt hM st hbnd κ₂

namespace EdgeSubset

variable {α : Type}

/-- The paired step and its value form are equivalent. -/
theorem pairedLedger_iff_value :
    EdgeSubset.PairedLedger ↔ PairedValueLedger := by
  constructor
  · intro H α _ W F k ℓ hM st hbnd κ₁ κ₂ hps h₁
    obtain ⟨⟨o₁, hc₁⟩⟩ := h₁
    obtain ⟨o₂, hc₂, hval⟩ := H hM st hbnd κ₁ κ₂ hps o₁ hc₁
    refine ⟨⟨⟨o₂, hc₂⟩⟩, ?_⟩
    rw [signedValueAt_eq hM st hbnd o₁ hc₁,
      signedValueAt_eq hM st hbnd o₂ hc₂]
    exact hval.symm
  · intro H α _ W F k ℓ hM st hbnd κ₁ κ₂ hps o₁ hc₁
    obtain ⟨⟨⟨o₂, hc₂⟩⟩, hval⟩ :=
      H hM st hbnd κ₁ κ₂ hps ⟨⟨o₁, hc₁⟩⟩
    refine ⟨o₂, hc₂, ?_⟩
    rw [← signedValueAt_eq hM st hbnd o₁ hc₁,
      ← signedValueAt_eq hM st hbnd o₂ hc₂]
    exact hval.symm

/-- **Same-pairing invariance of the signed value from the value
step**: the full well-definedness with the paired input in
value form. -/
theorem signedValueAt_samePairing_of_value
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (HPaired : PairedValueLedger) {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ κ' : F.RelTransitionSystem} (hsp : SamePairing κ κ') :
    F.signedValueAt hM st hbnd κ =
      F.signedValueAt hM st hbnd κ' :=
  signedValueAt_samePairing
    (matchPreservingLedger_of (pairedLedger_iff_value.mpr HPaired))
    hM st hbnd hsp

end EdgeSubset

end RS
