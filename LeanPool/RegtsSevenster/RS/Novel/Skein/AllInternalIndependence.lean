/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.StepLedger

/-!
# Unconditional independence on all-internal subsets

On an all-internal edge subset every participating flag is
periodic, so every repair square is localized and the single-step
ledger connects any two transition systems: the constrained
summand at the open circuit count is independent of all choices —
Proposition 3 for the boundary-free sector, as a theorem.
-/

@[expose] public section

namespace RS



variable {α : Type}

namespace EdgeSubset

/-- On an all-internal subset every repair square is localized:
both principal flags are periodic. -/
theorem squareLocalized_of_allInternal {W : Fragment α} {F : EdgeSubset W}
    (hall : F.allInternal)
    {κ : F.RelTransitionSystem} {a b c d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) :
    SquareLocalized κ a b c d :=
  Or.inl ⟨periodic_of_allInternal κ hall hsq.ha,
    periodic_of_allInternal κ hall hsq.hc⟩

/-- On an all-internal subset every repair step preserves the
(empty) boundary pairing. -/
theorem matchPreservingStep_of_allInternal {W : Fragment α} {F : EdgeSubset W}
    (hall : F.allInternal)
    {κ₁ κ₂ : F.RelTransitionSystem}
    (h : IsRepairStep κ₁ κ₂) : MatchPreservingStep κ₁ κ₂ := by
  obtain ⟨a, b, c, d, v, hsq, heq⟩ := h
  exact ⟨a, b, c, d, v, hsq,
    RelTransitionSystem.MatchEq.symm heq,
    pathMatch_repair_of_localized hsq
      (squareLocalized_of_allInternal hall hsq)⟩

/-- The single-step value chain on an all-internal subset. -/
private theorem allInternal_chain
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (hall : F.allInternal) (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} (o : κ.Orientation)
    {n : ℕ} (chain : Fin (n + 1) → F.RelTransitionSystem)
    (h0 : (chain 0).MatchEq κ)
    (hstep : ∀ r : Fin n,
      IsRepairStep (chain r.castSucc) (chain r.succ)) :
    ∀ r : Fin (n + 1),
      ∃ (oᵣ : (chain r).Orientation),
      pathSign (chain r) *
          F.throughSummand hM st hbnd oᵣ
            (chain r).openCircuitCount =
        pathSign κ *
          F.throughSummand hM st hbnd o κ.openCircuitCount := by
  intro r
  induction r using Fin.induction with
  | zero =>
    obtain ⟨o₀, hval⟩ := signed_summand_matchEq hM st hbnd
      (RelTransitionSystem.MatchEq.symm h0) o
    exact ⟨o₀, hval⟩
  | succ r ih =>
    obtain ⟨oprev, hprev⟩ := ih
    have hcprev : PathCanonical oprev :=
      pathCanonical_of_allInternal hall oprev
    obtain ⟨o₂, _, hstepval⟩ := stepLedger_single hM st hbnd _ _
      (matchPreservingStep_of_allInternal hall (hstep r))
      oprev hcprev
    exact ⟨o₂, hstepval.trans hprev⟩

/-- **Unconditional independence on all-internal subsets**: the
constrained summand at the open circuit count is independent of
the transition system and orientation.  (Canonicality is vacuous
and the path sign is trivial without boundary flags.) -/
theorem throughSummand_independence_of_allInternal
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (hall : F.allInternal) (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ κ' : F.RelTransitionSystem)
    (o : κ.Orientation) (o' : κ'.Orientation) :
    F.throughSummand hM st hbnd o κ.openCircuitCount =
      F.throughSummand hM st hbnd o' κ'.openCircuitCount := by
  obtain ⟨n, chain, h0, hlast, hstep⟩ := repair_connectivity κ κ'
  obtain ⟨olast, hval⟩ := allInternal_chain hall hM st hbnd o
    chain h0 hstep (Fin.last n)
  obtain ⟨oκ', hvalκ'⟩ := signed_summand_matchEq hM st hbnd
    hlast olast
  have h1 := hvalκ'.trans hval
  have e' : pathSign κ' *
        F.throughSummand hM st hbnd oκ' κ'.openCircuitCount =
      F.throughSummand hM st hbnd oκ' κ'.openCircuitCount :=
    (congrArg (fun x => x *
        F.throughSummand hM st hbnd oκ' κ'.openCircuitCount)
      (pathSign_of_allInternal hall κ')).trans
      (one_mul _)
  have e : pathSign κ *
        F.throughSummand hM st hbnd o κ.openCircuitCount =
      F.throughSummand hM st hbnd o κ.openCircuitCount :=
    (congrArg (fun x => x *
        F.throughSummand hM st hbnd o κ.openCircuitCount)
      (pathSign_of_allInternal hall κ)).trans
      (one_mul _)
  have h2 :
      F.throughSummand hM st hbnd oκ' κ'.openCircuitCount =
        F.throughSummand hM st hbnd o κ.openCircuitCount :=
    e'.symm.trans (h1.trans e)
  exact h2.symm.trans
    (throughSummand_pathCanonical hM st hbnd
      (pathCanonical_of_allInternal hall oκ')
      (pathCanonical_of_allInternal hall o') _)

end EdgeSubset

end RS
