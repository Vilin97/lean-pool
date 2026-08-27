/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Adversarial non-vacuity regressions for entry point (iii).

These tests specialize the final theorems to a concrete signature with both a
constant and a unary symbol, and use an explicit two-point model to rule out
easy completeness escapes.  They also instantiate the result at an ambient
signature whose symbol type is not assumed countable.
-/
import LeanPool.MatchingLogic.EntryIII.Conclusion

/-!
# MatchingLogic.EntryIII.Regression
-/

namespace MatchingLogic.EntryIIIRegression

open Set

/-- The nullary and unary symbols used by the regression models. -/
inductive AuditSym
  | nullary
  | unary
  deriving DecidableEq

instance : Fintype AuditSym where
  elems := {.nullary, .unary}
  complete x := by cases x <;> simp

/-- The regression signature with one constant and one unary operation. -/
abbrev AuditSig : Signature where
  Sym := AuditSym
  arity
    | .nullary => 0
    | .unary => 1

/-- A Boolean model used to audit nullary and unary semantics. -/
abbrev auditModel : Model AuditSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp
    | .nullary, _ => {false}
    | .unary, a => {a ⟨0, by simp⟩}

/-- The constant-false valuation in `auditModel`. -/
def auditRho : Nat → auditModel.carrier := fun _ => false

/-- The application of the nullary regression symbol. -/
def nullaryPattern : Pattern AuditSig Nat :=
  .app .nullary (fun i => Fin.elim0 i)

/-- The unary regression symbol applied to variable zero. -/
def unaryPattern : Pattern AuditSig Nat :=
  .app .unary (fun _ => .var 0)

/-- Bottom is not even a semantic consequence of the empty theory. -/
theorem bot_not_global_consequence :
    ¬ GlobalCons (∅ : Set (Pattern AuditSig Nat))
      (.bot : Pattern AuditSig Nat) := by
  intro hglobal
  have htotal := hglobal auditModel (by simp [Model.SatSet]) auditRho
  change (∅ : Set Bool) = Set.univ at htotal
  have : false ∈ (∅ : Set Bool) := by rw [htotal]; simp
  simp at this

/-- An open variable is not a semantic consequence of the empty theory. -/
theorem open_var_not_global_consequence :
    ¬ GlobalCons (∅ : Set (Pattern AuditSig Nat))
      (.var 0 : Pattern AuditSig Nat) := by
  intro hglobal
  have htotal := hglobal auditModel (by simp [Model.SatSet]) auditRho
  change ({false} : Set Bool) = Set.univ at htotal
  have : true ∈ ({false} : Set Bool) := by rw [htotal]; simp
  simp at this

/-- Soundness transfers the explicit bottom countermodel to non-provability. -/
theorem bot_not_empty_theorem :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) .bot := by
  intro hp
  exact bot_not_global_consequence (soundness _ _ hp)

/-- Soundness transfers the explicit open-variable countermodel to theoremhood. -/
theorem open_var_not_empty_theorem :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) (.var 0) := by
  intro hp
  exact open_var_not_global_consequence (soundness _ _ hp)

/-- At bottom, the final global-completeness equivalence relates two false sides. -/
theorem global_completeness_bottom_both_false :
    (¬ GlobalCons (∅ : Set (Pattern AuditSig Nat))
      (.bot : Pattern AuditSig Nat)) ∧
    (¬ Provable (∅ : Set (Pattern AuditSig Nat))
      (.bot : Pattern AuditSig Nat)) ∧
    (GlobalCons (∅ : Set (Pattern AuditSig Nat))
        (.bot : Pattern AuditSig Nat) ↔
      Provable (∅ : Set (Pattern AuditSig Nat))
        (.bot : Pattern AuditSig Nat)) := by
  have hiff : GlobalCons (∅ : Set (Pattern AuditSig Nat))
        (.bot : Pattern AuditSig Nat) ↔
      Provable (∅ : Set (Pattern AuditSig Nat))
        (.bot : Pattern AuditSig Nat) := by
    apply global_completeness_entryIII
    · simp
    · simp [Closed]
  exact ⟨bot_not_global_consequence, bot_not_empty_theorem, hiff⟩

theorem nullary_closed : Closed nullaryPattern := by
  unfold Closed nullaryPattern
  change (⋃ i : Fin 0, FV (Fin.elim0 i)) = ∅
  simp

/-- A closed constant pattern with singleton denotation is not theoremhood. -/
theorem nullary_not_empty_theorem :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) nullaryPattern := by
  intro hp
  have hglobal : GlobalCons (∅ : Set (Pattern AuditSig Nat)) nullaryPattern :=
    soundness _ _ hp
  have htotal := hglobal auditModel (by simp [Model.SatSet]) auditRho
  have htrue : true ∈ auditModel.denote auditRho nullaryPattern := by
    rw [htotal]
    simp
  simp [nullaryPattern, auditModel, AuditSig, Model.app] at htrue

theorem unary_open : ¬ Closed unaryPattern := by
  unfold Closed unaryPattern
  change (⋃ _ : Fin 1, ({0} : Set Nat)) ≠ ∅
  simp

/-- A unary application of an open variable is likewise not theoremhood. -/
theorem unary_not_empty_theorem :
    ¬ Provable (∅ : Set (Pattern AuditSig Nat)) unaryPattern := by
  intro hp
  have hglobal : GlobalCons (∅ : Set (Pattern AuditSig Nat)) unaryPattern :=
    soundness _ _ hp
  have htotal := hglobal auditModel (by simp [Model.SatSet]) auditRho
  have htrue : true ∈ auditModel.denote auditRho unaryPattern := by
    rw [htotal]
    simp
  simp [unaryPattern, auditRho, auditModel, AuditSig, Model.denote, Model.app] at htrue

/-- A concrete semantic point rules out local inconsistency. -/
theorem locConsistent_of_semantic_point
    {Gamma : Set (Pattern AuditSig Nat)}
    (M : Model AuditSig) (rho : Nat → M.carrier) (u : M.carrier)
    (hu : u ∈ M.denoteSet rho Gamma) :
    LocConsistent Gamma := by
  intro hbot
  rcases hbot with ⟨l, hl, hp⟩
  have hglobal : GlobalCons (∅ : Set (Pattern AuditSig Nat))
      (.imp (conj l) .bot) := soundness _ _ hp
  have htotal := hglobal M (by simp [Model.SatSet]) rho
  have huList : u ∈ M.denoteSet rho {delta | delta ∈ l} := by
    simp only [Model.denoteSet, Set.mem_iInter] at hu ⊢
    intro delta hdelta
    exact hu delta (hl delta hdelta)
  have huConj : u ∈ M.denote rho (conj l) := by
    rw [M.denote_conj_eq_denoteSet_list]
    exact huList
  have huImp : u ∈ M.denote rho (.imp (conj l) .bot) := by
    rw [htotal]
    simp
  simp only [denote_imp, denote_bot, Set.union_empty, Set.mem_compl_iff] at huImp
  exact huImp huConj

theorem nullary_has_semantic_point :
    false ∈ auditModel.denoteSet auditRho
      ({nullaryPattern} : Set (Pattern AuditSig Nat)) := by
  simp [Model.denoteSet, nullaryPattern, auditModel, AuditSig, Model.app]

theorem unary_has_semantic_point :
    false ∈ auditModel.denoteSet auditRho
      ({unaryPattern} : Set (Pattern AuditSig Nat)) := by
  simp only [AuditSig, auditModel, Fin.zero_eta, Fin.isValue,
    Model.denoteSet, unaryPattern, Set.mem_singleton_iff,
    Set.iInter_iInter_eq_left, denote_app, Model.app, denote_var, auditRho,
    Fin.forall_fin_one, Set.mem_ofPred_eq, Bool.false_eq, and_self]
  exact ⟨fun _ => false, rfl⟩

theorem nullary_singleton_locConsistent :
    LocConsistent ({nullaryPattern} : Set (Pattern AuditSig Nat)) :=
  locConsistent_of_semantic_point auditModel auditRho false
    nullary_has_semantic_point

theorem unary_singleton_locConsistent :
    LocConsistent ({unaryPattern} : Set (Pattern AuditSig Nat)) :=
  locConsistent_of_semantic_point auditModel auditRho false
    unary_has_semantic_point

/-- The semantic antecedent used below is inhabited by reflexivity. -/
theorem reflexive_local_antecedent :
    LocalCons ({(.var 0 : Pattern AuditSig Nat)} : Set (Pattern AuditSig Nat))
      (.var 0) := by
  intro M rho u hu
  simp only [Model.denoteSet, Set.mem_iInter] at hu
  exact hu (.var 0) (by simp)

/-- Completeness at `{x} ⊨loc x` cannot escape via an empty finite witness. -/
theorem strong_completeness_has_nonempty_witness :
    ∃ l : List (Pattern AuditSig Nat),
      l ≠ [] ∧
      (∀ delta ∈ l, delta ∈ ({(.var 0 : Pattern AuditSig Nat)} : Set _)) ∧
      Provable (∅ : Set (Pattern AuditSig Nat)) (.imp (conj l) (.var 0)) := by
  obtain ⟨l, hl, hp⟩ :=
    strongLocalCompleteness_nat
      ({(.var 0 : Pattern AuditSig Nat)} : Set (Pattern AuditSig Nat))
      (.var 0) reflexive_local_antecedent
  refine ⟨l, ?_, hl, hp⟩
  intro hempty
  subst l
  apply open_var_not_empty_theorem
  exact Provable.mp (provable_top (∅ : Set (Pattern AuditSig Nat)))
    (by simpa [conj] using hp)

theorem empty_list_locConsistent :
    LocConsistent {delta : Pattern AuditSig Nat | delta ∈ ([] : List _)} := by
  rw [show {delta : Pattern AuditSig Nat | delta ∈ ([] : List _)} = ∅ by simp]
  unfold LocConsistent
  rw [locProvable_empty_iff]
  exact bot_not_empty_theorem

theorem top_list_locConsistent :
    LocConsistent
      {delta : Pattern AuditSig Nat |
        delta ∈ [(Pattern.tp : Pattern AuditSig Nat)]} := by
  intro hbad
  have hset :
      {delta : Pattern AuditSig Nat |
          delta ∈ [(Pattern.tp : Pattern AuditSig Nat)]} =
        insert Pattern.tp (∅ : Set (Pattern AuditSig Nat)) := by
    ext delta
    simp
  rw [hset] at hbad
  have himpLocal : LocProvable (∅ : Set (Pattern AuditSig Nat))
      (.imp Pattern.tp .bot) := hbad.deduction_insert
  have himp : Provable (∅ : Set (Pattern AuditSig Nat))
      (.imp Pattern.tp .bot) := locProvable_empty_iff.mp himpLocal
  exact bot_not_empty_theorem
    (Provable.mp (provable_top (∅ : Set (Pattern AuditSig Nat))) himp)

/-- Finite model existence returns a concrete model, valuation, and carrier point. -/
theorem finite_model_existence_returns_actual_point :
    ∃ (M : Model AuditSig) (rho : Nat → M.carrier) (u : M.carrier),
      u ∈ M.denoteSet rho
        {delta : Pattern AuditSig Nat |
          delta ∈ [(Pattern.tp : Pattern AuditSig Nat)]} :=
  finiteLocalModelExistence [(Pattern.tp : Pattern AuditSig Nat)]
    top_list_locConsistent

/-- The finite encoding used by the canonical-model regression tests. -/
noncomputable local instance instEncodableAuditSym : Encodable AuditSym :=
  Fintype.toEncodable AuditSym

noncomputable local instance auditPatternCountable :
    Countable (Pattern AuditSig Nat) :=
  ⟨Pattern.signatureNatCode, Pattern.signatureNatCode_injective⟩

theorem canonical_existence_nullary_branch
    (Gamma : CanonicalCarrier AuditSig)
    (happ : nullaryPattern ∈ Gamma.val) :
    ∃ components : Fin (AuditSig.arity AuditSym.nullary) → CanonicalCarrier AuditSig,
      (∀ i, (fun j : Fin (AuditSig.arity AuditSym.nullary) => Fin.elim0 j) i ∈
        (components i).val) ∧
      Gamma ∈ canonicalInterp AuditSym.nullary components :=
  canonicalExistence Gamma AuditSym.nullary (fun i => Fin.elim0 i) happ

theorem canonical_existence_unary_branch
    (Gamma : CanonicalCarrier AuditSig)
    (happ : unaryPattern ∈ Gamma.val) :
    ∃ components : Fin (AuditSig.arity AuditSym.unary) → CanonicalCarrier AuditSig,
      (∀ i, (Pattern.var 0 : Pattern AuditSig Nat) ∈ (components i).val) ∧
      Gamma ∈ canonicalInterp AuditSym.unary components :=
  canonicalExistence Gamma AuditSym.unary (fun _ => .var 0) happ

/-- The nullary canonical-existence branch is invoked from an inhabited MCS premise. -/
theorem actual_canonical_nullary_branch :
    ∃ root : CanonicalCarrier AuditSig,
      ∃ components : Fin (AuditSig.arity AuditSym.nullary) →
          CanonicalCarrier AuditSig,
        root ∈ canonicalInterp AuditSym.nullary components := by
  have hconsistent : LocConsistent
      {delta : Pattern AuditSig Nat | delta ∈ [nullaryPattern]} := by
    simpa using nullary_singleton_locConsistent
  obtain ⟨Delta, hbase, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS
      [nullaryPattern] hconsistent
  let root : CanonicalCarrier AuditSig := ⟨Delta, hM, hW⟩
  have happ : nullaryPattern ∈ root.val := hbase (by simp)
  obtain ⟨components, _, hinterp⟩ :=
    canonical_existence_nullary_branch root happ
  exact ⟨root, components, hinterp⟩

/-- The positive-arity canonical branch is likewise invoked from a real premise. -/
theorem actual_canonical_unary_branch :
    ∃ root : CanonicalCarrier AuditSig,
      ∃ components : Fin (AuditSig.arity AuditSym.unary) →
          CanonicalCarrier AuditSig,
        (Pattern.var 0 : Pattern AuditSig Nat) ∈
            (components ⟨0, by simp⟩).val ∧
          root ∈ canonicalInterp AuditSym.unary components := by
  have hconsistent : LocConsistent
      {delta : Pattern AuditSig Nat | delta ∈ [unaryPattern]} := by
    simpa using unary_singleton_locConsistent
  obtain ⟨Delta, hbase, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS
      [unaryPattern] hconsistent
  let root : CanonicalCarrier AuditSig := ⟨Delta, hM, hW⟩
  have happ : unaryPattern ∈ root.val := hbase (by simp)
  obtain ⟨components, hargs, hinterp⟩ :=
    canonical_existence_unary_branch root happ
  exact ⟨root, components, hargs ⟨0, by simp⟩, hinterp⟩

/-- Canonical, generated, and completed model carriers all expose real points. -/
theorem canonical_constructions_are_inhabited :
    ∃ root : CanonicalCarrier AuditSig,
      Nonempty (canonicalModel root).carrier ∧
      Nonempty (generatedModel root).carrier ∧
      Nonempty (completedModel root).carrier ∧
      completedEmbed root (generatedRoot root) ∈ Set.univ := by
  obtain ⟨Delta, _hbase, hM, hW⟩ :=
    finite_locConsistent_extend_freshWitnessed_isMCS
      ([] : List (Pattern AuditSig Nat)) empty_list_locConsistent
  let root : CanonicalCarrier AuditSig := ⟨Delta, hM, hW⟩
  refine ⟨root, ⟨root⟩, ⟨generatedRoot root⟩,
    ⟨completedEmbed root (generatedRoot root)⟩, ?_⟩
  simp

/-- An ambient symbol type with no countability assumption. -/
def HugeSig : Signature where
  Sym := Set Nat
  arity _ := 1

/-- The finite-support reduction reaches the unconditional ambient result. -/
theorem arbitrary_ambient_signature_reduction_is_exercised :
    FiniteLocalModelExistence HugeSig Nat ∧
      StrongLocalCompleteness HugeSig Nat :=
  ⟨finiteLocalModelExistence, strongLocalCompleteness_nat⟩

end MatchingLogic.EntryIIIRegression
