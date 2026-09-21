/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingSignature

/-!
# The pairing-resolved signed value

The signed canonical summand of a single transition system, chosen
among its path-canonical orientations.  Within one system the
choice is immaterial (`throughSummand_pathCanonical`); across
systems with the same boundary pairing it is invariant given the
pairing-preserving ledger — the well-definedness of the value as a
function of the pairing, riding on the proved block connectivity.
-/

namespace RS

open scoped Classical

variable {α : Type}

namespace EdgeSubset

open Classical in
/-- The signed canonical summand of one system: the path sign times
the through summand at the open circuit count, at a chosen
path-canonical orientation. -/
noncomputable def signedValueAt [LinearOrder α] {W : Fragment α}
    {k ℓ : ℕ}
    (F : EdgeSubset W) (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ : F.RelTransitionSystem) : ℂ :=
  if h : Nonempty {o : κ.Orientation // PathCanonical o} then
    pathSign κ *
      F.throughSummand hM st hbnd (Classical.choice h).val
        κ.openCircuitCount
  else 0

/-- The signed value evaluates at any concrete path-canonical
orientation. -/
theorem signedValueAt_eq [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    (hc : PathCanonical o) :
    F.signedValueAt hM st hbnd κ =
      pathSign κ *
        F.throughSummand hM st hbnd o κ.openCircuitCount := by
  have hne : Nonempty {o : κ.Orientation // PathCanonical o} :=
    ⟨⟨o, hc⟩⟩
  rw [signedValueAt, dif_pos hne]
  exact congrArg (fun x => pathSign κ * x)
    (throughSummand_pathCanonical hM st hbnd
      (Classical.choice hne).prop hc _)

/-- Canonical-orientation existence transfers along the same
pairing, given the ledger: fold the ledger down the block chain and
cross the final `MatchEq`. -/
theorem canonical_transfer_of_samePairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (HLedger : MatchPreservingLedger) {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ κ' : F.RelTransitionSystem} (hsp : SamePairing κ κ')
    (o : κ.Orientation) (hc : PathCanonical o) :
    ∃ o' : κ'.Orientation, PathCanonical o' := by
  obtain ⟨n, chain, h0, hlast, hstep⟩ := pairingConnectivity κ κ'
    hsp
  obtain ⟨olast, hclast, -⟩ :=
    chain_carry HLedger hM st hbnd o hc chain h0 hstep (Fin.last n)
  obtain ⟨oκ', hcκ', -⟩ :=
    endpoint_transfer hM st hbnd hlast olast hclast
  exact ⟨oκ', hcκ'⟩

/-- **Same-pairing invariance of the signed value** (conditional on
the pairing-preserving ledger): the signed canonical summand is a
function of the boundary pairing alone. -/
theorem signedValueAt_samePairing
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (HLedger : MatchPreservingLedger) {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ κ' : F.RelTransitionSystem} (hsp : SamePairing κ κ') :
    F.signedValueAt hM st hbnd κ =
      F.signedValueAt hM st hbnd κ' := by
  by_cases h : Nonempty {o : κ.Orientation // PathCanonical o}
  · obtain ⟨⟨o, hc⟩⟩ := h
    obtain ⟨o', hc'⟩ := canonical_transfer_of_samePairing HLedger
      hM st hbnd hsp o hc
    rw [signedValueAt_eq hM st hbnd o hc,
      signedValueAt_eq hM st hbnd o' hc']
    exact samePairing_invariance_of pairingConnectivity HLedger
      hM st hbnd κ κ' hsp o hc o' hc'
  · have h' : ¬ Nonempty {o : κ'.Orientation // PathCanonical o} := by
      intro ⟨⟨o', hc'⟩⟩
      obtain ⟨o, hc⟩ := canonical_transfer_of_samePairing HLedger
        hM st hbnd (SamePairing.symm hsp) o' hc'
      exact h ⟨⟨o, hc⟩⟩
    rw [signedValueAt, dif_neg h, signedValueAt, dif_neg h']

end EdgeSubset

end RS
