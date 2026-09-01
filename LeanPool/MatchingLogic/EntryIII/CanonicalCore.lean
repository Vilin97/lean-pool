/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The source-faithful core of the canonical model for entry point (iii).

This file stops before the n-ary Existence Lemma.  It defines MCS worlds with
the stronger fresh-witness invariant delivered by the Henkin construction,
the source's universal symbol interpretation, and the local consistency fact
needed to start the simultaneous argument-theory extension.
-/
import LeanPool.MatchingLogic.EntryIII.Witnessed
import LeanPool.MatchingLogic.EntryIII.MCSAlpha

/-!
# MatchingLogic.EntryIII.CanonicalCore
-/

namespace MatchingLogic

open Set

variable {S : Signature}

noncomputable section

/-- Local decidable equality used by the canonical-model construction. -/
local instance instDecidableEqPatternNatCanonicalCore : DecidableEq (Pattern S Nat) :=
  Classical.decEq _

/-- A point of the canonical model is a maximal locally consistent set with
fresh Henkin witnesses.  The ordinary witnessed interface is recovered below. -/
def CanonicalCarrier (S : Signature) :=
  {Gamma : Set (Pattern S Nat) // IsMCS Gamma ∧ FreshWitnessed Gamma}

instance CanonicalCarrier.coeSet :
    Coe (CanonicalCarrier S) (Set (Pattern S Nat)) where
  coe Gamma := Gamma.val

namespace CanonicalCarrier

@[simp] theorem coe_mk (Gamma : Set (Pattern S Nat))
    (h : IsMCS Gamma ∧ FreshWitnessed Gamma) :
    ((⟨Gamma, h⟩ : CanonicalCarrier S) : Set (Pattern S Nat)) = Gamma :=
  rfl

/-- The underlying theory of a canonical point is an MCS. -/
theorem isMCS (Gamma : CanonicalCarrier S) :
    IsMCS Gamma.val :=
  Gamma.property.1

/-- The underlying theory of a canonical point has fresh Henkin witnesses. -/
theorem freshWitnessed (Gamma : CanonicalCarrier S) :
    FreshWitnessed Gamma.val :=
  Gamma.property.2

/-- Forgetting freshness recovers the interface used by the basic Truth Lemma. -/
theorem witnessed (Gamma : CanonicalCarrier S) :
    Witnessed Gamma.val :=
  FreshWitnessed.toWitnessed (freshWitnessed Gamma)

end CanonicalCarrier

/-- Every witnessed MCS contains an element-variable pattern.  This is the
source's Existence rule followed by the MCS's witness implication. -/
theorem IsMCS.exists_var_mem_of_witnessed
    {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma) (hW : Witnessed Gamma) :
    ∃ y : Nat, Pattern.var y ∈ Gamma := by
  have hex : Pattern.ex 0 (Pattern.var 0) ∈ Gamma :=
    hM.mem_of_provable_empty (Provable.existence (Γ := ∅) (x := 0))
  obtain ⟨y, hy⟩ := hW hex
  refine ⟨y, ?_⟩
  have hinstance := hM.mp_mem hex hy
  simpa [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar] using hinstance

/-- Carrier-specialized form of variable existence. -/
theorem CanonicalCarrier.exists_var_mem (Gamma : CanonicalCarrier S) :
    ∃ y : Nat, Pattern.var y ∈ Gamma.val :=
  (CanonicalCarrier.isMCS Gamma).exists_var_mem_of_witnessed
    (CanonicalCarrier.witnessed Gamma)

/-- Source Definition 72: `Gamma` is an output of `sigma` at component worlds
`components` exactly when every pointwise choice of patterns from those worlds
forms a `sigma`-application belonging to `Gamma`. -/
def canonicalInterp (sigma : S.Sym)
    (components : Fin (S.arity sigma) → CanonicalCarrier S) :
    Set (CanonicalCarrier S) :=
  {Gamma | ∀ args : Fin (S.arity sigma) → Pattern S Nat,
    (∀ i, args i ∈ (components i).val) →
      Pattern.app sigma args ∈ Gamma.val}

/-- The one-sorted canonical model.  The designated root is used only to
supply the required nonempty-carrier witness. -/
abbrev canonicalModel (root : CanonicalCarrier S) : Model S where
  carrier := CanonicalCarrier S
  nonempty := ⟨root⟩
  interp := canonicalInterp

@[simp] theorem mem_canonicalInterp {sigma : S.Sym}
    {components : Fin (S.arity sigma) → CanonicalCarrier S}
    {Gamma : CanonicalCarrier S} :
    Gamma ∈ canonicalInterp sigma components ↔
      ∀ args : Fin (S.arity sigma) → Pattern S Nat,
        (∀ i, args i ∈ (components i).val) →
          Pattern.app sigma args ∈ Gamma.val :=
  Iff.rfl

@[simp] theorem canonicalModel_interp (root : CanonicalCarrier S)
    (sigma : S.Sym) (components : Fin (S.arity sigma) → CanonicalCarrier S) :
    (canonicalModel root).interp sigma components = canonicalInterp sigma components :=
  rfl

theorem mem_canonicalModel_interp (root : CanonicalCarrier S)
    {sigma : S.Sym} {components : Fin (S.arity sigma) → CanonicalCarrier S}
    {Gamma : CanonicalCarrier S} :
    Gamma ∈ (canonicalModel root).interp sigma components ↔
      ∀ args : Fin (S.arity sigma) → Pattern S Nat,
        (∀ i, args i ∈ (components i).val) →
          Pattern.app sigma args ∈ Gamma.val :=
  Iff.rfl

/-! ### Singleton argument consistency -/

/-- With no local premises, local derivability collapses to ordinary
empty-theory provability. -/
theorem LocProvable.provable_empty {p : Pattern S Nat}
    (h : LocProvable (∅ : Set (Pattern S Nat)) p) :
    Provable (∅ : Set (Pattern S Nat)) p := by
  rcases h with ⟨l, hl, hp⟩
  have hnil : l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    exact (hl q hq).elim
  subst l
  exact Provable.mp (provable_top (∅ : Set (Pattern S Nat))) (by
    simpa [conj] using hp)

/-- If an application belongs to an MCS, each singleton theory generated by
one of its arguments is locally consistent.  Otherwise framing an argument's
derived bottom into the application and then propagating bottom contradicts
the MCS consistency. -/
theorem IsMCS.singleton_argument_locConsistent
    {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma)
    {sigma : S.Sym} {args : Fin (S.arity sigma) → Pattern S Nat}
    (happ : Pattern.app sigma args ∈ Gamma) (i : Fin (S.arity sigma)) :
    LocConsistent ({args i} : Set (Pattern S Nat)) := by
  intro hbad
  have hbad' : LocProvable
      (insert (args i) (∅ : Set (Pattern S Nat))) (.bot : Pattern S Nat) := by
    simpa only [insert_empty_eq] using hbad
  have hargbot : Provable (∅ : Set (Pattern S Nat))
      (.imp (args i) .bot) :=
    (LocProvable.deduction_insert hbad').provable_empty
  have hframe : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma args) (.app sigma (Function.update args i .bot))) := by
    have h := Provable.framing (Γ := (∅ : Set (Pattern S Nat)))
      (σ := sigma) (i := i) (args := args) hargbot
    simpa only [Function.update_eq_self] using h
  have hprop : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma (Function.update args i .bot)) .bot) :=
    Provable.propBot
  have happbot : Provable (∅ : Set (Pattern S Nat))
      (.imp (.app sigma args) .bot) := hframe.imp_trans hprop
  have hbot : (.bot : Pattern S Nat) ∈ Gamma :=
    hM.mem_of_provable_imp happ happbot
  exact hM.1 (LocProvable.of_mem hbot)

end

end MatchingLogic
