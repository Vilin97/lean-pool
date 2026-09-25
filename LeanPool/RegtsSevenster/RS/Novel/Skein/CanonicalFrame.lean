/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TwoPathNonSep
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChordLabels

/-!
# The canonical frame: chain directions and re-canonicalization

Vocabulary for the final `PairedLedger` induction.  Every
participating boundary chain of a relative transition system carries
a direction observable — the orientation value at its entry edge
(`chainDir`).  Path-canonicality is exactly the vanishing of
`chainDir` at every low-labelled chain end
(`pathCanonical_iff_chainDir`), and `chainDir` is constant along a
chain (`chainDir_eq`), so an arbitrary orientation differs from the
canonical frame exactly on the chains its low ends point out of
(`antiLowSet`, `pathCanonical_iff_antiLowSet_empty`).  Flipping one offending
chain (`exists_chainRecanonicalize`) toggles the two end directions,
preserves every other chain, and transforms the constrained summand
by the two end-colour signs at a `∂`-relabelled state; iterating
over the anti-canonical chains re-canonicalizes any orientation
(`exists_recanonicalize`).
-/

namespace RS



namespace EdgeSubset

variable {α : Type}

/-! ## The chain-direction observable -/

/-- **The chain direction** of an orientation at a boundary flag:
the orientation value at the flag's entry edge (the internal partner
of the boundary flag).  `false` means the entry edge is incoming —
the chain leaves this end. -/
def chainDir {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) (β : W.Flag) : Bool :=
  o.isOut (W.pairing β)

/-- A chain's direction is the orientation at its entry edge. -/
theorem chainDir_eq
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) (β : W.Flag) :
    chainDir o β = o.isOut (W.pairing β) := rfl

/-- The entry edge of the far chain end is internal whenever the
near one is: the chain has at least one step, and its last walk flag
is internal. -/
theorem pathMatch_pairing_internal
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {β : W.Flag}
    (hβ : β ∈ F.boundaryFlags)
    (hint : W.pairing β ∈ F.internalFlags) :
    W.pairing (κ.pathMatch β hβ) ∈ F.internalFlags := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [iterWalk_zero] at hterm
      exact absurd hterm (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hint)
    · exact h
  have hpm : κ.pathMatch β hβ = W.pairing (iterWalk κ β k) :=
    κ.pathMatch_eq hβ (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ β hcont hterm))
  rw [hpm, W.pairing_invol]
  exact iterWalk_mem_internal κ k hk1 le_rfl hcont

/-- **Chain-direction rigidity**: the chain is coherently directed,
so the two ends' entry flags carry opposite orientation values — for
*any* orientation of the system. -/
theorem chainDir_pathMatch
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {β : W.Flag}
    (hβ : β ∈ F.boundaryFlags)
    (hint : W.pairing β ∈ F.internalFlags) :
    chainDir o (κ.pathMatch β hβ) = !chainDir o β := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [iterWalk_zero] at hterm
      exact absurd hterm (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hint)
    · exact h
  have hpm : κ.pathMatch β hβ = W.pairing (iterWalk κ β k) :=
    κ.pathMatch_eq hβ (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ β hcont hterm))
  change o.isOut (W.pairing (κ.pathMatch β hβ)) =
    !o.isOut (W.pairing β)
  rw [hpm, W.pairing_invol]
  exact isOut_iterWalk_eq_not_seed o hcont k hk1 le_rfl

/-! ## Canonicality via the chain direction -/

/-- **Path-canonicality is a chain-direction condition**: an
orientation is path-canonical iff its chain direction vanishes at
every participating boundary flag that is the low-labelled end of its
chord. -/
theorem pathCanonical_iff_chainDir
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) :
    PathCanonical o ↔
      ∀ (β : W.Flag) (hβ : β ∈ F.boundaryFlags),
        W.pairing β ∈ F.internalFlags →
        F.boundaryLabel hβ <
          F.boundaryLabel (κ.pathMatch_mem hβ) →
        chainDir o β = false := by
  constructor
  · intro hc β hβ hint hlt
    have hβeq : β = W.boundaryFlag (F.boundaryLabel hβ) :=
      W.eq_boundaryFlag _ β (attach_boundaryLabel hβ)
    have hbB : W.boundaryFlag (F.boundaryLabel hβ) ∈
        F.boundaryFlags := hβeq ▸ hβ
    have hintB : W.pairing (W.boundaryFlag (F.boundaryLabel hβ)) ∈
        F.internalFlags := by
      rw [← hβeq]
      exact hint
    have hpm : κ.pathMatch (W.boundaryFlag (F.boundaryLabel hβ))
        hbB =
        W.boundaryFlag (F.boundaryLabel (κ.pathMatch_mem hβ)) := by
      rw [κ.pathMatch_congr hβeq.symm hbB hβ]
      exact W.eq_boundaryFlag _ _
        (attach_boundaryLabel (κ.pathMatch_mem hβ))
    have hval := hc _ _ hbB hintB hpm hlt
    change o.isOut (W.pairing β) = false
    rw [hβeq]
    exact hval
  · intro H i j hb hint hpm hij
    have hlab_i : F.boundaryLabel hb = i :=
      boundaryLabel_eq_of_attach hb (W.attach_boundaryFlag i)
    have hlab_j : F.boundaryLabel (κ.pathMatch_mem hb) = j :=
      boundaryLabel_eq_of_attach _ (by
        rw [hpm]
        exact W.attach_boundaryFlag j)
    exact H _ hb hint (by
      rw [hlab_i, hlab_j]
      exact hij)

/-! ## Chain directions under the ported chain flip -/

section FlipDir

/-- Flipping a ported set toggles the chain direction at ends whose
entry edge lies in the set. -/
theorem chainDir_portFlip_of_mem
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {S : Finset W.Flag} {p₁ : W.Flag} {p₂ : W.Flag} {i₁ : α} {i₂ : α}
    (o : κ.Orientation)
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) {γ : W.Flag}
    (hγ : W.pairing γ ∈ S) :
    chainDir (o.portFlip h) γ = !chainDir o γ :=
  portFlip_isOut_of_mem o h hγ

/-- Flipping a ported set preserves the chain direction at ends
whose entry edge avoids the set. -/
theorem chainDir_portFlip_of_notMem
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {S : Finset W.Flag} {p₁ : W.Flag} {p₂ : W.Flag} {i₁ : α} {i₂ : α}
    (o : κ.Orientation)
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) {γ : W.Flag}
    (hγ : W.pairing γ ∉ S) :
    chainDir (o.portFlip h) γ = chainDir o γ :=
  portFlip_isOut_of_notMem o h hγ

end FlipDir

/-- **The chain flip set of a participating boundary flag**: the
boundary chain of `β` realizes a ported flip set whose ports are the
entry edges of `β` and of its path match, labelled by the two chain
ends, and whose flip set avoids the entry edge of every other
boundary flag. -/
theorem exists_chainFlipSet
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {β : W.Flag}
    (hβ : β ∈ F.boundaryFlags)
    (hint : W.pairing β ∈ F.internalFlags) :
    ∃ S : Finset W.Flag,
      PortedFlipSet κ S (W.pairing β)
        (W.pairing (κ.pathMatch β hβ))
        (F.boundaryLabel hβ)
        (F.boundaryLabel (κ.pathMatch_mem hβ)) ∧
      W.pairing (κ.pathMatch β hβ) ∈ S ∧
      ∀ γ ∈ F.boundaryFlags, γ ≠ β → γ ≠ κ.pathMatch β hβ →
        W.pairing γ ∉ S := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [iterWalk_zero] at hterm
      exact absurd hterm (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hint)
    · exact h
  have hpm : κ.pathMatch β hβ = W.pairing (iterWalk κ β k) :=
    κ.pathMatch_eq hβ (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ β hcont hterm))
  have hiβ : W.attach β = Sum.inr (F.boundaryLabel hβ) :=
    attach_boundaryLabel hβ
  have hiγ : W.attach (W.pairing (iterWalk κ β k)) =
      Sum.inr (F.boundaryLabel (κ.pathMatch_mem hβ)) := by
    rw [← hpm]
    exact attach_boundaryLabel (κ.pathMatch_mem hβ)
  obtain ⟨S, hS, hSon, -⟩ :=
    exists_chainPortedFlipSet κ hβ hcont hterm hk1 hiβ hiγ
  have hp₂ : iterWalk κ β k = W.pairing (κ.pathMatch β hβ) := by
    rw [hpm, W.pairing_invol]
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [← hp₂]
    exact hS
  · rw [← hp₂]
    exact hS.hp₂S
  · intro γ hγ hγβ hγpm hmem
    obtain ⟨k', t, htk, hcont', hterm', hft⟩ := hSon _ hmem
    have hkk : k' = k := chain_exit_unique hcont' hterm' hcont hterm
    subst hkk
    rcases hft with hft | hft
    · -- entry edge on the walk side: `γ` is a pairing-side flag
      have hγeq : γ = W.pairing (iterWalk κ β t) := by
        have h2 := congrArg W.pairing hft
        rwa [W.pairing_invol] at h2
      rcases Nat.lt_or_ge t k' with hlt | hge
      · refine absurd hγ (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags ?_)
        rw [hγeq]
        exact hcont t hlt
      · apply hγpm
        rw [hγeq, show t = k' from by omega, hpm]
    · -- entry edge on the pairing side: `γ` is a walk flag
      have hγeq : γ = iterWalk κ β t := by
        have h2 := congrArg W.pairing hft
        rwa [W.pairing_invol, W.pairing_invol] at h2
      rcases Nat.eq_zero_or_pos t with rfl | ht1
      · rw [iterWalk_zero] at hγeq
        exact hγβ hγeq
      · refine absurd hγ (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags ?_)
        rw [hγeq]
        exact iterWalk_mem_internal κ k' ht1 htk hcont

/-! ## The re-canonicalization ledger, one chain -/

section FlipLedger

/-- The two-sign cast squares to one. -/
theorem signPairSq (ℓ : ℕ) (c₁ c₂ : Fin (2 * ℓ)) :
    ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) =
      1 := by
  have h1 := twoPathNonSepFactor_mul_self ℓ c₁ c₂
  rwa [twoPathNonSepFactor_eq, neg_mul_neg] at h1

/-- **The inverted chain-flip ledger**: the summand of the original
orientation equals the two chain-end colour signs times the summand
of the *flipped* orientation at the `∂`-relabelled state — the
direction useful for re-canonicalization, obtained from
`throughSummand_portFlip` by involution of the relabel and the
sign. -/
theorem throughSummand_portFlip_inv
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {i₁ : α} {i₂ : α} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) (n : ℕ) :
    F.throughSummand hM st hbnd o n =
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
        F.throughSummand hM (stateOddFlip st i₁ i₂)
          (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂)
          (o.portFlip h) n := by
  have hc₁' : stateOddFlip st i₁ i₂ i₁ =
      Sum.inr (oddPartner ℓ c₁) := stateOddFlip_left_odd hc₁
  have hc₂' : stateOddFlip st i₁ i₂ i₂ =
      Sum.inr (oddPartner ℓ c₂) := stateOddFlip_right_odd hc₂
  have hkey := throughSummand_portFlip hM (stateOddFlip st i₁ i₂)
    (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) o h
    hc₁' hc₂' n
  have hback : F.throughSummand hM
      (stateOddFlip (stateOddFlip st i₁ i₂) i₁ i₂)
      (genBoundarySubsetMatches_stateOddFlip
        (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) i₁ i₂)
      o n =
      F.throughSummand hM st hbnd o n :=
    throughSummand_state_congr F hM stateOddFlip_stateOddFlip _
      hbnd o n
  have hsgn : ((oddPartnerSign ℓ (oddPartner ℓ c₁) *
        oddPartnerSign ℓ (oddPartner ℓ c₂) : ℤ) : ℂ) =
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) := by
    rw [oddPartnerSign_oddPartner, oddPartnerSign_oddPartner,
      neg_mul_neg]
  rw [hback, hsgn] at hkey
  calc F.throughSummand hM st hbnd o n
      = 1 * F.throughSummand hM st hbnd o n := (one_mul _).symm
    _ = ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
          (((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
            F.throughSummand hM st hbnd o n) := by
        rw [← mul_assoc, signPairSq]
    _ = ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
          F.throughSummand hM (stateOddFlip st i₁ i₂)
            (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂)
            (o.portFlip h) n := by
        rw [← hkey]

end FlipLedger

section ChainRecanon

/-- **One-chain re-canonicalization**: for any orientation and any
participating boundary flag `β` with internal entry partner, there
is an orientation of the *same* system that toggles the chain
direction at `β` and its path match, preserves the chain direction
of every other boundary flag, and satisfies the inverted value
ledger with the chain's two boundary labels explicit. -/
theorem exists_chainRecanonicalize
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) {β : W.Flag}
    (hβ : β ∈ F.boundaryFlags)
    (hint : W.pairing β ∈ F.internalFlags)
    {c₁ c₂ : Fin (2 * ℓ)}
    (hc₁ : st (F.boundaryLabel hβ) = Sum.inr c₁)
    (hc₂ : st (F.boundaryLabel (κ.pathMatch_mem hβ)) =
      Sum.inr c₂) :
    ∃ o₁ : κ.Orientation,
      chainDir o₁ β = !chainDir o β ∧
      chainDir o₁ (κ.pathMatch β hβ) =
        !chainDir o (κ.pathMatch β hβ) ∧
      (∀ γ ∈ F.boundaryFlags, γ ≠ β → γ ≠ κ.pathMatch β hβ →
        chainDir o₁ γ = chainDir o γ) ∧
      ∀ n, F.throughSummand hM st hbnd o n =
        ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
          F.throughSummand hM
            (stateOddFlip st (F.boundaryLabel hβ)
              (F.boundaryLabel (κ.pathMatch_mem hβ)))
            (genBoundarySubsetMatches_stateOddFlip hbnd
              (F.boundaryLabel hβ)
              (F.boundaryLabel (κ.pathMatch_mem hβ))) o₁ n := by
  obtain ⟨S, hS, hp₂S, hdisj⟩ := exists_chainFlipSet hβ hint
  refine ⟨o.portFlip hS, ?_, ?_, ?_, ?_⟩
  · exact chainDir_portFlip_of_mem o hS hS.hp₁S
  · exact chainDir_portFlip_of_mem o hS hp₂S
  · intro γ hγ h1 h2
    exact chainDir_portFlip_of_notMem o hS (hdisj γ hγ h1 h2)
  · intro n
    exact throughSummand_portFlip_inv hM st hbnd o hS hc₁ hc₂ n

end ChainRecanon

/-! ## The anti-canonical chain set and full re-canonicalization -/

/-- The set of *low* chain ends whose chain is directed against the
canonical frame: participating boundary flags that are the
low-labelled end of their chord and whose entry edge is outgoing.
Each anti-canonical chain contributes exactly one element — its low
end. -/
noncomputable def antiLowSet [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) :
    Finset W.Flag :=
  F.boundaryFlags.filter (fun β =>
    ∃ hβ : β ∈ F.boundaryFlags,
      W.pairing β ∈ F.internalFlags ∧
      F.boundaryLabel hβ <
        F.boundaryLabel (κ.pathMatch_mem hβ) ∧
      chainDir o β = true)

/-- Membership in the anti-canonical set: the low end of a chain
that runs the wrong way — exactly the chains re-canonicalization
flips. -/
theorem mem_antiLowSet [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {β : W.Flag} :
    β ∈ antiLowSet o ↔
      ∃ hβ : β ∈ F.boundaryFlags,
        W.pairing β ∈ F.internalFlags ∧
        F.boundaryLabel hβ <
          F.boundaryLabel (κ.pathMatch_mem hβ) ∧
        chainDir o β = true := by
  unfold antiLowSet
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨hβ, h⟩
    exact ⟨hβ, hβ, h⟩

/-- An orientation is path-canonical exactly when its anti-canonical
low-end set is empty. -/
theorem pathCanonical_iff_antiLowSet_empty
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) :
    PathCanonical o ↔ antiLowSet o = ∅ := by
  rw [pathCanonical_iff_chainDir]
  constructor
  · intro H
    refine Finset.eq_empty_of_forall_notMem (fun β hβmem => ?_)
    obtain ⟨hβ, hint, hlow, hdir⟩ := mem_antiLowSet.mp hβmem
    rw [H β hβ hint hlow] at hdir
    cases hdir
  · intro H β hβ hint hlow
    cases hdir : chainDir o β
    · rfl
    · exact absurd
        (mem_antiLowSet.mpr ⟨hβ, hint, hlow, hdir⟩)
        (by rw [H]; exact Finset.notMem_empty β)

/-- A low chain end is never the path match of a low chain end: the
path match of a low end is the high end of the same chord. -/
theorem low_ne_pathMatch_of_low
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {β γ : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hγ : γ ∈ F.boundaryFlags)
    (hlowβ : F.boundaryLabel hβ <
      F.boundaryLabel (κ.pathMatch_mem hβ))
    (hlowγ : F.boundaryLabel hγ <
      F.boundaryLabel (κ.pathMatch_mem hγ)) :
    γ ≠ κ.pathMatch β hβ := by
  intro heq
  have h1 : F.boundaryLabel hγ =
      F.boundaryLabel (κ.pathMatch_mem hβ) :=
    boundaryLabel_congr hγ (κ.pathMatch_mem hβ) heq
  have hinv : κ.pathMatch γ hγ = β := by
    rw [κ.pathMatch_congr heq hγ (κ.pathMatch_mem hβ)]
    exact κ.pathMatch_invol hβ
  have h2 : F.boundaryLabel (κ.pathMatch_mem hγ) =
      F.boundaryLabel hβ :=
    boundaryLabel_congr (κ.pathMatch_mem hγ) hβ hinv
  rw [h1, h2] at hlowγ
  exact lt_asymm hlowβ hlowγ

/-- **The flip step shrinks the anti-canonical set by exactly its
chain**: an orientation that toggles the chain direction at an
anti-canonical low end `β` (and possibly at `β`'s path match) and
preserves every other chain direction has anti-canonical set
`antiLowSet o` minus `β`. -/
theorem antiLowSet_flip [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o o₁ : κ.Orientation} {β : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hβmem : β ∈ antiLowSet o)
    (hd₁ : chainDir o₁ β = !chainDir o β)
    (hpres : ∀ γ ∈ F.boundaryFlags, γ ≠ β →
      γ ≠ κ.pathMatch β hβ → chainDir o₁ γ = chainDir o γ) :
    antiLowSet o₁ = (antiLowSet o).erase β := by
  obtain ⟨hβ', hint, hlow, hdir⟩ := mem_antiLowSet.mp hβmem
  apply Finset.ext
  intro γ
  rw [Finset.mem_erase, mem_antiLowSet, mem_antiLowSet]
  constructor
  · rintro ⟨hγ, hintγ, hlowγ, hdirγ⟩
    have hγβ : γ ≠ β := by
      rintro rfl
      rw [hd₁, hdir] at hdirγ
      exact Bool.false_ne_true hdirγ
    have hγpm : γ ≠ κ.pathMatch β hβ :=
      low_ne_pathMatch_of_low hβ hγ hlow hlowγ
    refine ⟨hγβ, hγ, hintγ, hlowγ, ?_⟩
    rw [← hpres γ hγ hγβ hγpm]
    exact hdirγ
  · rintro ⟨hγβ, hγ, hintγ, hlowγ, hdirγ⟩
    have hγpm : γ ≠ κ.pathMatch β hβ :=
      low_ne_pathMatch_of_low hβ hγ hlow hlowγ
    refine ⟨hγ, hintγ, hlowγ, ?_⟩
    rw [hpres γ hγ hγβ hγpm]
    exact hdirγ

section Recanonicalize

/-- **Full re-canonicalization**: any orientation of a relative
transition system is connected to a path-canonical orientation of
the *same* system by a value ledger — the summand at the original
data equals a sign (a product of chain-end colour sign pairs, hence
squaring to `1`) times the summand of the canonical orientation at
an iterated `∂`-relabel of the state.  Induction on the number of
anti-canonical chains, flipping one chain per step via
`exists_chainRecanonicalize`. -/
theorem exists_recanonicalize
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) :
    ∃ (o₁ : κ.Orientation) (s : ℂ)
      (st₁ : GenBoundaryState k ℓ α)
      (hbnd₁ : genBoundarySubsetMatches W F.flags st₁),
      PathCanonical o₁ ∧ s * s = 1 ∧
      ∀ n, F.throughSummand hM st hbnd o n =
        s * F.throughSummand hM st₁ hbnd₁ o₁ n := by
  suffices H : ∀ (N : ℕ) (st : GenBoundaryState k ℓ α)
      (hbnd : genBoundarySubsetMatches W F.flags st)
      (o : κ.Orientation), (antiLowSet o).card = N →
      ∃ (o₁ : κ.Orientation) (s : ℂ)
        (st₁ : GenBoundaryState k ℓ α)
        (hbnd₁ : genBoundarySubsetMatches W F.flags st₁),
        PathCanonical o₁ ∧ s * s = 1 ∧
        ∀ n, F.throughSummand hM st hbnd o n =
          s * F.throughSummand hM st₁ hbnd₁ o₁ n by
    exact H _ st hbnd o rfl
  intro N
  induction N with
  | zero =>
    intro st hbnd o hcard
    refine ⟨o, 1, st, hbnd, ?_, mul_one 1,
      fun n => (one_mul _).symm⟩
    rw [pathCanonical_iff_antiLowSet_empty]
    exact Finset.card_eq_zero.mp hcard
  | succ N ih =>
    intro st hbnd o hcard
    have hne : (antiLowSet o).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨β, hβmem⟩ := hne
    obtain ⟨hβ, hint, hlow, hdir⟩ := mem_antiLowSet.mp hβmem
    obtain ⟨c₁, hc₁⟩ :
        ∃ c, st (F.boundaryLabel hβ) = Sum.inr c := by
      apply (hbnd _).mp
      have he : W.boundaryFlag (F.boundaryLabel hβ) = β :=
        (W.eq_boundaryFlag _ β (attach_boundaryLabel hβ)).symm
      rw [he]
      exact mem_flags_of_boundaryFlags F hβ
    obtain ⟨c₂, hc₂⟩ :
        ∃ c, st (F.boundaryLabel (κ.pathMatch_mem hβ)) =
          Sum.inr c := by
      apply (hbnd _).mp
      have he : W.boundaryFlag
          (F.boundaryLabel (κ.pathMatch_mem hβ)) =
          κ.pathMatch β hβ :=
        (W.eq_boundaryFlag _ _
          (attach_boundaryLabel (κ.pathMatch_mem hβ))).symm
      rw [he]
      exact mem_flags_of_boundaryFlags F (κ.pathMatch_mem hβ)
    obtain ⟨o₁, hd₁, hd₂, hpres, hled⟩ :=
      exists_chainRecanonicalize hM st hbnd o hβ hint hc₁ hc₂
    have hset : antiLowSet o₁ = (antiLowSet o).erase β :=
      antiLowSet_flip hβ hβmem hd₁ hpres
    have hcard₁ : (antiLowSet o₁).card = N := by
      rw [hset, Finset.card_erase_of_mem hβmem, hcard]
      omega
    obtain ⟨o₂, s, st₂, hbnd₂, hcanon, hs, hled₂⟩ :=
      ih (stateOddFlip st (F.boundaryLabel hβ)
          (F.boundaryLabel (κ.pathMatch_mem hβ)))
        (genBoundarySubsetMatches_stateOddFlip hbnd
          (F.boundaryLabel hβ)
          (F.boundaryLabel (κ.pathMatch_mem hβ))) o₁ hcard₁
    refine ⟨o₂,
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) * s,
      st₂, hbnd₂, hcanon, ?_, ?_⟩
    · have hmul : ∀ a b : ℂ, a * a = 1 → b * b = 1 →
          (a * b) * (a * b) = 1 := by
        intro a b ha hb
        calc (a * b) * (a * b) = (a * a) * (b * b) := by ring
          _ = 1 := by rw [ha, hb, one_mul]
      exact hmul _ _ (signPairSq ℓ c₁ c₂) hs
    · intro n
      rw [hled n, hled₂ n, mul_assoc]

end Recanonicalize

end EdgeSubset

end RS
