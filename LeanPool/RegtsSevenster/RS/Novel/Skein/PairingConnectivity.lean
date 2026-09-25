/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger

/-!
# Pairing-preserving connectivity

The pairing-resolved value is well-defined once systems inducing
the same boundary pairing are connected by pairing-preserving
repair steps.  This file fixes the
step relation and the connectivity statement, proves that
localized repairs qualify, and derives the same-pairing invariance
of the signed summand from connectivity and the per-step ledger.
-/

namespace RS



variable {α : Type}

namespace EdgeSubset

/-- Two systems induce the same boundary pairing. -/
def SamePairing {W : Fragment α} {F : EdgeSubset W}
    (κ κ' : F.RelTransitionSystem) : Prop :=
  ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
    κ.pathMatch δ hδ = κ'.pathMatch δ hδ

/-- Inducing the same boundary pairing is reflexive. -/
theorem SamePairing.refl {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) :
    SamePairing κ κ := fun _ _ => rfl

/-- It is symmetric. -/
theorem SamePairing.symm {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (h : SamePairing κ κ') : SamePairing κ' κ :=
  fun δ hδ => (h δ hδ).symm

/-- And transitive — an equivalence on transition systems. -/
theorem SamePairing.trans {W : Fragment α} {F : EdgeSubset W}
    {κ₁ κ₂ κ₃ : F.RelTransitionSystem}
    (h : SamePairing κ₁ κ₂) (h' : SamePairing κ₂ κ₃) :
    SamePairing κ₁ κ₃ :=
  fun δ hδ => (h δ hδ).trans (h' δ hδ)

/-- A repair step that preserves the boundary pairing. -/
def MatchPreservingStep {W : Fragment α} {F : EdgeSubset W}
    (κ₁ κ₂ : F.RelTransitionSystem) : Prop :=
  ∃ (a b c d : W.Flag) (v : W.Vertex)
    (hsq : RepairSquare κ₁ a b c d v),
    κ₂.MatchEq (κ₁.repair a b c d v hsq) ∧
    ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      (κ₁.repair a b c d v hsq).pathMatch δ hδ =
        κ₁.pathMatch δ hδ

/-- A pairing-preserving step indeed preserves the pairing. -/
theorem samePairing_of_step {W : Fragment α} {F : EdgeSubset W}
    {κ₁ κ₂ : F.RelTransitionSystem}
    (h : MatchPreservingStep κ₁ κ₂) : SamePairing κ₁ κ₂ := by
  obtain ⟨a, b, c, d, v, hsq, heq, hpres⟩ := h
  intro δ hδ
  rw [← hpres δ hδ]
  exact pathMatch_matchEq heq hδ

/-- A composite move: a repair block whose net effect preserves
the boundary pairing (individual repairs may cross two chains and
change it; the double-crossing example shows single-step
connectivity fails, and non-adjacent restorations force general
blocks rather than pairs). -/
def PairedStep {W : Fragment α} {F : EdgeSubset W}
    (κ₁ κ₂ : F.RelTransitionSystem) : Prop :=
  (∃ (n : ℕ) (chain : Fin (n + 1) → F.RelTransitionSystem),
    (chain 0).MatchEq κ₁ ∧ (chain (Fin.last n)).MatchEq κ₂ ∧
    ∀ r : Fin n, IsRepairStep (chain r.castSucc) (chain r.succ)) ∧
  SamePairing κ₁ κ₂

/-- A pairing-preserving move: a single preserved step or a
π-restoring pair. -/
def MatchPreservingMove {W : Fragment α} {F : EdgeSubset W}
    (κ₁ κ₂ : F.RelTransitionSystem) : Prop :=
  MatchPreservingStep κ₁ κ₂ ∨ PairedStep κ₁ κ₂

/-- **The connectivity statement** (the keystone, move form):
systems with the same boundary pairing are connected by
pairing-preserving moves, up to match-equality at the endpoints.
(Single steps do not suffice: the double-crossing configuration
disconnects the fibre.) -/
def PairingConnectivity : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} (κ κ' : F.RelTransitionSystem),
    SamePairing κ κ' →
    ∃ (n : ℕ) (chain : Fin (n + 1) → F.RelTransitionSystem),
      (chain 0).MatchEq κ ∧ (chain (Fin.last n)).MatchEq κ' ∧
      ∀ r : Fin n,
        MatchPreservingMove (chain r.castSucc) (chain r.succ)

/-- **Connectivity is a theorem in the block form**: any repair
chain between same-pairing systems is a single pairing-preserving
move, so the general connectivity of `TransitionMove` suffices. -/
theorem pairingConnectivity : PairingConnectivity := by
  intro α _ W F κ κ' hsp
  refine ⟨1, ![κ, κ'], RelTransitionSystem.MatchEq.refl κ,
    RelTransitionSystem.MatchEq.refl κ', ?_⟩
  intro r
  have hr : r = 0 := Subsingleton.elim r 0
  subst hr
  right
  refine ⟨?_, hsp⟩
  obtain ⟨n, chain, h0, hlast, hstep⟩ := repair_connectivity κ κ'
  exact ⟨n, chain, h0, hlast, hstep⟩

/-- **The per-step ledger interface**: every pairing-preserving
step preserves the signed canonical summand (dischargeable from
the localized/non-separated ledgers plus the orbit
parities; two-path moves change the pairing and are excluded by
the step relation). -/
def MatchPreservingLedger : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ₁ κ₂ : F.RelTransitionSystem),
    MatchPreservingMove κ₁ κ₂ →
    ∀ (o₁ : κ₁.Orientation), PathCanonical o₁ →
    ∃ (o₂ : κ₂.Orientation), PathCanonical o₂ ∧
      pathSign κ₂ *
          F.throughSummand hM st hbnd o₂ κ₂.openCircuitCount =
        pathSign κ₁ *
          F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount

/-- The `MatchEq` layer for the signed canonical summand. -/
theorem signed_summand_matchEq
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ₂ : F.RelTransitionSystem}
    (heq : κ₁.MatchEq κ₂) (o₁ : κ₁.Orientation) :
    ∃ o₂ : κ₂.Orientation,
      pathSign κ₂ *
          F.throughSummand hM st hbnd o₂ κ₂.openCircuitCount =
        pathSign κ₁ *
          F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount := by
  refine ⟨RelTransitionSystem.Orientation.ofMatchEq heq o₁, ?_⟩
  rw [← pathSign_matchEq heq, ← openCircuitCount_matchEq heq]
  exact congrArg (fun x => pathSign κ₂ * x)
    (throughSummand_ofMatchEq hM st hbnd heq o₁
      κ₂.openCircuitCount)

/-- The forward-carried chain induction: along a chain of
pairing-preserving steps, a canonical orientation and the signed
value propagate from the base. -/
theorem chain_carry [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (HLedger : MatchPreservingLedger)
    {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) (hc : PathCanonical o)
    {n : ℕ} (chain : Fin (n + 1) → F.RelTransitionSystem)
    (h0 : (chain 0).MatchEq κ)
    (hstep : ∀ r : Fin n,
      MatchPreservingMove (chain r.castSucc) (chain r.succ)) :
    ∀ r : Fin (n + 1),
      ∃ (oᵣ : (chain r).Orientation), PathCanonical oᵣ ∧
      pathSign (chain r) *
          F.throughSummand hM st hbnd oᵣ
            (chain r).openCircuitCount =
        pathSign κ *
          F.throughSummand hM st hbnd o κ.openCircuitCount := by
  intro r
  induction r using Fin.induction with
  | zero =>
    refine ⟨RelTransitionSystem.Orientation.ofMatchEq
      (RelTransitionSystem.MatchEq.symm h0) o, ?_, ?_⟩
    · intro i j hb hint hpm hij
      exact hc i j hb hint (by
        rw [← pathMatch_matchEq
          (RelTransitionSystem.MatchEq.symm h0)
          (δ := W.boundaryFlag i) hb]
        exact hpm) hij
    · rw [← pathSign_matchEq (RelTransitionSystem.MatchEq.symm h0),
        ← openCircuitCount_matchEq
          (RelTransitionSystem.MatchEq.symm h0)]
      exact congrArg (fun x => pathSign (chain 0) * x)
        (throughSummand_ofMatchEq hM st hbnd
          (RelTransitionSystem.MatchEq.symm h0) o
          (chain 0).openCircuitCount)
  | succ r ih =>
    obtain ⟨oprev, hcprev, hprev⟩ := ih
    obtain ⟨o₂, hc₂, hstepval⟩ := HLedger hM st hbnd _ _
      (hstep r) oprev hcprev
    exact ⟨o₂, hc₂, hstepval.trans hprev⟩

/-- The endpoint transfer: a canonical orientation and the signed
value cross a `MatchEq` to the target system. -/
theorem endpoint_transfer [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ' : F.RelTransitionSystem} (hlast : κ₁.MatchEq κ')
    (olast : κ₁.Orientation) (hclast : PathCanonical olast) :
    ∃ oκ' : κ'.Orientation, PathCanonical oκ' ∧
      pathSign κ' *
          F.throughSummand hM st hbnd oκ' κ'.openCircuitCount =
        pathSign κ₁ *
          F.throughSummand hM st hbnd olast
            κ₁.openCircuitCount := by
  refine ⟨RelTransitionSystem.Orientation.ofMatchEq hlast olast,
    ?_, ?_⟩
  · intro i j hb hint hpm hij
    exact hclast i j hb hint (by
      rw [← pathMatch_matchEq hlast (δ := W.boundaryFlag i) hb]
      exact hpm) hij
  · rw [← pathSign_matchEq hlast, ← openCircuitCount_matchEq hlast]
    exact congrArg (fun x => pathSign κ' * x)
      (throughSummand_ofMatchEq hM st hbnd hlast olast
        κ'.openCircuitCount)

/-- **Same-pairing invariance from connectivity and the step
ledger**: with these two inputs the signed canonical summand
depends only on the boundary pairing — the well-definedness of the
pairing-resolved value. -/
theorem samePairing_invariance_of
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (HConn : PairingConnectivity)
    (HLedger : MatchPreservingLedger)
    {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ κ' : F.RelTransitionSystem) (hsp : SamePairing κ κ')
    (o : κ.Orientation) (hc : PathCanonical o)
    (o' : κ'.Orientation) (hc' : PathCanonical o') :
    pathSign κ * F.throughSummand hM st hbnd o κ.openCircuitCount =
      pathSign κ' *
        F.throughSummand hM st hbnd o' κ'.openCircuitCount := by
  obtain ⟨n, chain, h0, hlast, hstep⟩ := HConn κ κ' hsp
  obtain ⟨olast, hclast, hval⟩ :=
    chain_carry HLedger hM st hbnd o hc chain h0 hstep (Fin.last n)
  obtain ⟨oκ', hcκ', hvalκ'⟩ :=
    endpoint_transfer hM st hbnd hlast olast hclast
  exact hval.symm.trans (hvalκ'.symm.trans
    (congrArg (fun x => pathSign κ' * x)
      (throughSummand_pathCanonical hM st hbnd hcκ' hc' _)))

end EdgeSubset

end RS
