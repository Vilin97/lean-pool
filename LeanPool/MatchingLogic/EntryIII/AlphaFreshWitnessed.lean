/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Whether the gap between ordinary and fresh witnessedness survives the
proof-theoretic alpha bridge.
-/
import LeanPool.MatchingLogic.EntryIII.Conclusion
import LeanPool.MatchingLogic.EntryIII.WitnessedCollapse
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# MatchingLogic.EntryIII.AlphaFreshWitnessed
-/

namespace MatchingLogic

open Set

noncomputable section

/-- A witness may be taken after replacing the existential by any pattern
related by the repository's proof-theoretic alpha bridge. -/
def AlphaFreshWitnessed {S : Signature}
    (Gamma : Set (Pattern S Nat)) : Prop :=
  ∀ {x : Nat} {p : Pattern S Nat}, Pattern.ex x p ∈ Gamma →
    ∃ (x' : Nat) (p' : Pattern S Nat) (y : Nat),
      Pattern.AlphaEq (Pattern.ex x p) (Pattern.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (Pattern.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ Gamma

private theorem provable_empty_of_local_valid {S : Signature}
    {p : Pattern S Nat} (h : LocalCons (∅ : Set (Pattern S Nat)) p) :
    Provable (∅ : Set (Pattern S Nat)) p := by
  obtain ⟨l, hl, hp⟩ := strongLocalCompleteness_nat
    (∅ : Set (Pattern S Nat)) p h
  have hempty : l = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q hq
    exact (hl q hq).elim
  subst l
  exact Provable.mp (provable_top (∅ : Set (Pattern S Nat)))
    (by simpa [conj] using hp)

private theorem alphaEq_of_denote_eq {S : Signature}
    {p q : Pattern S Nat}
    (hden : ∀ (M : Model S) (rho : Nat → M.carrier),
      M.denote rho p = M.denote rho q)
    (hcomplexity : p.complexity = q.complexity) :
    Pattern.AlphaEq p q := by
  refine ⟨?_, ?_, hcomplexity⟩
  · intro Gamma
    apply (provable_empty_of_local_valid (p := Pattern.imp p q) ?_).weaken_empty
    intro M rho u _hu
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
    by_cases hp : u ∈ M.denote rho p
    · exact Or.inr (by simpa [hden M rho] using hp)
    · exact Or.inl hp
  · intro Gamma
    apply (provable_empty_of_local_valid (p := Pattern.imp q p) ?_).weaken_empty
    intro M rho u _hu
    simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
    by_cases hq : u ∈ M.denote rho q
    · exact Or.inr (by simpa [hden M rho] using hq)
    · exact Or.inl hq

/-- The candidate from the probe has a proof-theoretic alpha-equivalent,
vacuously quantified representative.  Thus it is not a counterexample to the
alpha-relaxed condition. -/
theorem fvBlocked_has_alpha_fresh_witness :
    ∃ (x' : Nat) (p' : Pattern WitnessCollapseSig Nat) (y : Nat),
      Pattern.AlphaEq
        (.ex 1 (Pattern.and (.var 1) (.var 0))) (.ex x' p') ∧
      y ∉ p'.allVars ∧
      Pattern.imp (.ex x' p')
        (Pattern.captureAvoidingSubst x' y p') ∈ witnessCollapseTheory := by
  let p' : Pattern WitnessCollapseSig Nat :=
    Pattern.and (.var 0) (.var 0)
  refine ⟨1, p', 1, ?_, ?_, ?_⟩
  · apply alphaEq_of_denote_eq
    · intro M rho
      ext u
      simp [p', Pattern.and, Pattern.nt]
    · simp [p', Pattern.complexity]
  · simp [p', Pattern.allVars]
  · change true ∈ witnessCollapseModel.denote witnessCollapseRho _
    simp [p', Pattern.captureAvoidingSubst, Pattern.avoidBinder,
      Pattern.and, Pattern.nt, witnessCollapseRho]

/-! A binary-symbol countermodel.  The small complexity of the distinguished
existential leaves no room for a proof-theoretically equivalent vacuous copy
of its body. -/

/-- The binary operation symbol used by the alpha-equivalence countermodels. -/
inductive AlphaWitnessSym
  | pair
  deriving DecidableEq

instance : Fintype AlphaWitnessSym where
  elems := {AlphaWitnessSym.pair}
  complete s := by cases s; simp

/-- The signature containing the binary alpha-witness operation. -/
abbrev AlphaWitnessSig : Signature where
  Sym := AlphaWitnessSym
  arity _ := 2

/-- Public because `alphaBlocked` is public and unfolds through it: a private
name in the type of a public declaration cannot be reached by the pin list. -/
def pairArgs (p q : Pattern AlphaWitnessSig Nat) :
    Fin 2 → Pattern AlphaWitnessSig Nat
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q

@[simp] theorem pairArgs_zero (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 0 = p := rfl

@[simp] theorem pairArgs_one (p q : Pattern AlphaWitnessSig Nat) :
    pairArgs p q 1 = q := rfl

private def boolPair (p q : Bool) : Fin 2 → Bool
  | ⟨0, _⟩ => p
  | ⟨1, _⟩ => q

@[simp] private theorem boolPair_zero (p q : Bool) : boolPair p q 0 = p := rfl
@[simp] private theorem boolPair_one (p q : Bool) : boolPair p q 1 = q := rfl

/-- The Boolean model used to witness the alpha-renaming obstruction. -/
abbrev alphaWitnessModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = true ∧ a 1 = true then {true} else ∅

/-- The valuation that maps exactly variable zero to `true`. -/
def alphaWitnessRho : Nat → alphaWitnessModel.carrier := fun n => n = 0

/-- The complete pointed theory of `alphaWitnessModel` at `true`. -/
def alphaWitnessTheory : Set (Pattern AlphaWitnessSig Nat) :=
  {p | true ∈ alphaWitnessModel.denote alphaWitnessRho p}

private theorem alphaWitnessRho_surjective :
    Function.Surjective alphaWitnessRho := by
  intro b
  cases b with
  | false => exact ⟨1, by simp [alphaWitnessRho]⟩
  | true => exact ⟨0, by simp [alphaWitnessRho]⟩

private theorem alphaWitness_mem_denote_conj
    (l : List (Pattern AlphaWitnessSig Nat))
    (hl : ∀ p ∈ l, true ∈ alphaWitnessModel.denote alphaWitnessRho p) :
    true ∈ alphaWitnessModel.denote alphaWitnessRho (conj l) := by
  induction l with
  | nil => simp [conj]
  | cons p l ih =>
      have hp := hl p (by simp)
      have htail := ih (by
        intro q hq
        exact hl q (by simp [hq]))
      simpa [conj, Pattern.and, Pattern.nt] using And.intro hp htail

theorem alphaWitnessTheory_isMCS : IsMCS alphaWitnessTheory := by
  constructor
  · rintro ⟨l, hl, hp⟩
    have hconj : true ∈ alphaWitnessModel.denote alphaWitnessRho (conj l) :=
      alphaWitness_mem_denote_conj l (by
        intro p hp'
        exact hl p hp')
    have htotal := soundness
      (∅ : Set (Pattern AlphaWitnessSig Nat))
      (.imp (conj l) .bot) hp alphaWitnessModel (by simp [Model.SatSet])
      alphaWitnessRho
    have himp : true ∈ alphaWitnessModel.denote alphaWitnessRho
        (.imp (conj l) .bot) := by
      rw [htotal]
      exact Set.mem_univ true
    simp only [denote_imp, denote_bot, Set.union_empty,
      Set.mem_compl_iff] at himp
    exact himp hconj
  · intro Delta hstrict hDeltaConsistent
    obtain ⟨p, hpDelta, hpNotGamma⟩ := Set.exists_of_ssubset hstrict
    have hnotpGamma : Pattern.nt p ∈ alphaWitnessTheory := by
      change true ∈ alphaWitnessModel.denote alphaWitnessRho (Pattern.nt p)
      change true ∉ alphaWitnessModel.denote alphaWitnessRho p at hpNotGamma
      simpa only [denote_nt, Set.mem_compl_iff] using hpNotGamma
    have hpLoc : LocProvable Delta p := LocProvable.of_mem hpDelta
    have hnotpLoc : LocProvable Delta (Pattern.nt p) :=
      LocProvable.of_mem (hstrict.1 hnotpGamma)
    exact hDeltaConsistent (hpLoc.mp hnotpLoc)

theorem alphaWitnessTheory_witnessed : Witnessed alphaWitnessTheory := by
  intro x p hex
  change true ∈ alphaWitnessModel.denote alphaWitnessRho (.ex x p) at hex
  simp only [denote_ex, Set.mem_iUnion] at hex
  obtain ⟨a, ha⟩ := hex
  obtain ⟨y, hy⟩ := alphaWitnessRho_surjective a
  refine ⟨y, ?_⟩
  change true ∈ alphaWitnessModel.denote alphaWitnessRho
    (.imp (.ex x p) (Pattern.captureAvoidingSubst x y p))
  apply Set.mem_union_right
  rw [alphaWitnessModel.denote_captureAvoidingSubst]
  simpa [hy] using ha

/-- The existential pattern whose binder cannot be renamed to variable zero. -/
def alphaBlocked : Pattern AlphaWitnessSig Nat :=
  .ex 1 (.app .pair (pairArgs (.var 1) (.var 0)))

theorem alphaBlocked_mem : alphaBlocked ∈ alphaWitnessTheory := by
  change true ∈ alphaWitnessModel.denote alphaWitnessRho alphaBlocked
  simp only [alphaWitnessModel, Fin.isValue, alphaBlocked, denote_ex,
    denote_app, Model.app, Fin.forall_fin_two, pairArgs_zero, denote_var,
    Function.update_self, Set.mem_singleton_iff, pairArgs_one, ne_eq,
    zero_ne_one, not_false_eq_true, Function.update_of_ne, alphaWitnessRho,
    decide_true, Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq,
    and_true, Bool.exists_bool, and_self]
  exact Or.inr ⟨fun _ => true, by simp⟩

private theorem alphaWitness_complexity_pos
    (p : Pattern AlphaWitnessSig Nat) : 0 < p.complexity := by
  induction p with
  | var => simp [Pattern.complexity]
  | bot => simp [Pattern.complexity]
  | app sigma args ih => simp [Pattern.complexity]
  | imp p q ihp ihq => simp [Pattern.complexity]
  | ex x p ih => simp [Pattern.complexity]

private theorem alphaWitness_complexity_one
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 1) :
    (∃ z, p = .var z) ∨ p = .bot := by
  cases p with
  | var z => exact Or.inl ⟨z, rfl⟩
  | bot => exact Or.inr rfl
  | app sigma args =>
      have hp := alphaWitness_complexity_pos (args 0)
      simp [Pattern.complexity] at h
      omega
  | imp p q =>
      have hp := alphaWitness_complexity_pos p
      have hq := alphaWitness_complexity_pos q
      simp [Pattern.complexity] at h
      omega
  | ex x p =>
      have hp := alphaWitness_complexity_pos p
      simp [Pattern.complexity] at h
      omega

private theorem alphaWitness_complexity_two
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 2) :
    ∃ z q, p = .ex z q ∧ ((∃ a, q = .var a) ∨ q = .bot) := by
  cases p with
  | var z => simp [Pattern.complexity] at h
  | bot => simp [Pattern.complexity] at h
  | app sigma args =>
      have hp := alphaWitness_complexity_pos (args 0)
      have hq := alphaWitness_complexity_pos (args 1)
      cases sigma
      rw [Pattern.complexity, Fin.sum_univ_two] at h
      omega
  | imp p q =>
      have hp := alphaWitness_complexity_pos p
      have hq := alphaWitness_complexity_pos q
      simp [Pattern.complexity] at h
      omega
  | ex z q =>
      have hq : q.complexity = 1 := by
        simp [Pattern.complexity] at h
        omega
      exact ⟨z, q, rfl, alphaWitness_complexity_one q hq⟩

private theorem alphaWitness_body_shape
    (p : Pattern AlphaWitnessSig Nat) (h : p.complexity = 3) :
    (∃ a b, p = .app .pair (pairArgs a b) ∧
      ((∃ z, a = .var z) ∨ a = .bot) ∧
      ((∃ z, b = .var z) ∨ b = .bot)) ∨
    (∃ a b, p = .imp a b ∧
      ((∃ z, a = .var z) ∨ a = .bot) ∧
      ((∃ z, b = .var z) ∨ b = .bot)) ∨
    (∃ z w a, p = .ex z (.ex w a) ∧
      ((∃ v, a = .var v) ∨ a = .bot)) := by
  cases p with
  | var z => simp [Pattern.complexity] at h
  | bot => simp [Pattern.complexity] at h
  | app sigma args =>
      cases sigma
      have hsum : (args 0).complexity + (args 1).complexity = 2 := by
        rw [Pattern.complexity, Fin.sum_univ_two] at h
        omega
      have hp := alphaWitness_complexity_pos (args 0)
      have hq := alphaWitness_complexity_pos (args 1)
      have hp1 : (args 0).complexity = 1 := by omega
      have hq1 : (args 1).complexity = 1 := by omega
      refine Or.inl ⟨args 0, args 1, ?_,
        alphaWitness_complexity_one _ hp1,
        alphaWitness_complexity_one _ hq1⟩
      congr
      funext i
      fin_cases i <;> rfl
  | imp a b =>
      have hsum : a.complexity + b.complexity = 2 := by
        simp [Pattern.complexity] at h
        omega
      have ha := alphaWitness_complexity_pos a
      have hb := alphaWitness_complexity_pos b
      have ha1 : a.complexity = 1 := by omega
      have hb1 : b.complexity = 1 := by omega
      exact Or.inr (Or.inl ⟨a, b, rfl,
        alphaWitness_complexity_one _ ha1,
        alphaWitness_complexity_one _ hb1⟩)
  | ex z q =>
      have hq : q.complexity = 2 := by
        simp [Pattern.complexity] at h
        omega
      obtain ⟨w, a, rfl, ha⟩ := alphaWitness_complexity_two q hq
      exact Or.inr (Or.inr ⟨z, w, a, rfl, ha⟩)

/-- The singleton model with an empty interpretation. -/
abbrev alphaUnitEmptyModel : Model AlphaWitnessSig where
  carrier := Unit
  nonempty := ⟨()⟩
  interp _ _ := ∅

/-- The singleton model with a total interpretation. -/
abbrev alphaUnitFullModel : Model AlphaWitnessSig where
  carrier := Unit
  nonempty := ⟨()⟩
  interp _ _ := {()}

/-- The unique valuation into the singleton carrier. -/
def alphaUnitRho : Nat → alphaUnitEmptyModel.carrier := fun _ => ()

/-- The Boolean model selecting the `(true, false)` input pair. -/
abbrev alphaFirstSelectorModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = true ∧ a 1 = false then {true} else ∅

/-- The Boolean model selecting the `(false, true)` input pair. -/
abbrev alphaCornerSelectorModel : Model AlphaWitnessSig where
  carrier := Bool
  nonempty := ⟨false⟩
  interp _ a := if a 0 = false ∧ a 1 = true then {true} else ∅

private theorem alphaBlocked_alphaEq_body_shape {x' : Nat}
    {p' : Pattern AlphaWitnessSig Nat}
    (halpha : Pattern.AlphaEq alphaBlocked (.ex x' p')) :
    ∃ a b, p' = .app .pair (pairArgs (.var a) (.var b)) ∧
      a = x' ∧ b = 0 := by
  have hpComplexity : p'.complexity = 3 := by
    have hc := halpha.complexity_eq
    simp [alphaBlocked, Pattern.complexity, Fin.sum_univ_two, pairArgs] at hc
    omega
  rcases alphaWitness_body_shape p' hpComplexity with
      ⟨a, b, rfl, ha, hb⟩ | ⟨a, b, rfl, ha, hb⟩ |
        ⟨z, w, a, rfl, ha⟩
  · rcases ha with ⟨a, rfl⟩ | rfl <;>
      rcases hb with ⟨b, rfl⟩ | rfl
    · have hax : a = x' := by
        by_contra hax
        have hden := halpha.denote_eq
          (M := alphaFirstSelectorModel) (rho := fun _ => false)
        have hleft : true ∈ alphaFirstSelectorModel.denote
            (fun _ => false) alphaBlocked := by
          simp only [alphaFirstSelectorModel, Fin.isValue, alphaBlocked,
            denote_ex, denote_app, Model.app, pairArgs, Fin.forall_fin_two,
            denote_var, Function.update_self, Set.mem_singleton_iff, ne_eq,
            zero_ne_one, not_false_eq_true, Function.update_of_ne,
            Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq,
            and_true, Bool.exists_bool, and_self]
          exact Or.inr ⟨boolPair true false, by simp [boolPair]⟩
        rw [hden] at hleft
        simp [alphaFirstSelectorModel, Model.app, pairArgs, hax] at hleft
        aesop
      refine ⟨a, b, rfl, hax, ?_⟩
      subst a
      by_contra hb0
      have hden := halpha.denote_eq
        (M := alphaCornerSelectorModel)
        (rho := fun n => n = 0)
      have hleft : true ∈ alphaCornerSelectorModel.denote
          (fun n => n = 0) alphaBlocked := by
        simp only [alphaCornerSelectorModel, Fin.isValue, alphaBlocked,
          denote_ex, denote_app, Model.app, pairArgs, Fin.forall_fin_two,
          denote_var, Function.update_self, Set.mem_singleton_iff, ne_eq,
          zero_ne_one, not_false_eq_true, Function.update_of_ne, decide_true,
          Set.mem_ite_empty_right, Set.mem_iUnion, Set.mem_ofPred_eq, and_true,
          Bool.exists_bool, and_self]
        exact Or.inl ⟨boolPair false true, by simp [boolPair]⟩
      rw [hden] at hleft
      by_cases hbx : b = x'
      · simp [alphaCornerSelectorModel, Model.app, pairArgs,
          hbx] at hleft
        aesop
      · simp [alphaCornerSelectorModel, Model.app, pairArgs,
          hb0, hbx] at hleft
        aesop
    · have hden := halpha.denote_eq
        (M := alphaUnitFullModel) (rho := alphaUnitRho)
      simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
        alphaUnitRho] at hden
    · have hden := halpha.denote_eq
        (M := alphaUnitFullModel) (rho := alphaUnitRho)
      simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
        alphaUnitRho] at hden
    · have hden := halpha.denote_eq
        (M := alphaUnitFullModel) (rho := alphaUnitRho)
      simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
        alphaUnitRho] at hden
  · rcases ha with ⟨a, rfl⟩ | rfl <;>
      rcases hb with ⟨b, rfl⟩ | rfl
    · have hden := halpha.denote_eq
        (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
      simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
        Function.update_eq_self, denote_app, Model.app, pairArgs,
        Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
        Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
        exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
        Set.union_singleton] at hden
      have hmem := Set.ext_iff.mp hden ()
      simp at hmem
    · by_cases hax : a = x'
      · subst a
        have hden := halpha.denote_eq
          (M := alphaUnitFullModel) (rho := alphaUnitRho)
        simp only [alphaUnitFullModel, alphaBlocked, denote_ex,
          Function.update_eq_self, denote_app, Model.app, pairArgs,
          Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
          Set.mem_singleton_iff, and_self, exists_const, Set.ofPred_true,
          denote_imp, denote_bot, Set.union_empty] at hden
        have hmem := Set.ext_iff.mp hden ()
        simp at hmem
      · have hden := halpha.denote_eq
          (M := alphaUnitFullModel) (rho := alphaUnitRho)
        simp only [alphaUnitFullModel, alphaBlocked, denote_ex,
          Function.update_eq_self, denote_app, Model.app, pairArgs,
          Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
          Set.mem_singleton_iff, and_self, exists_const, Set.ofPred_true,
          denote_imp, denote_bot, Set.union_empty] at hden
        have hmem := Set.ext_iff.mp hden ()
        simp at hmem
    · have hden := halpha.denote_eq
        (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
      simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
        Function.update_eq_self, denote_app, Model.app, pairArgs,
        Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
        Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
        exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
        denote_bot, Set.compl_empty, Set.union_singleton, Set.mem_univ,
        Set.insert_eq_of_mem] at hden
      have hmem := Set.ext_iff.mp hden ()
      simp at hmem
    · have hden := halpha.denote_eq
        (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
      simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
        Function.update_eq_self, denote_app, Model.app, pairArgs,
        Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
        Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
        exists_const, Set.ofPred_false, Set.iUnion_empty, denote_imp,
        denote_bot, Set.compl_empty, Set.union_empty] at hden
      have hmem := Set.ext_iff.mp hden ()
      simp at hmem
  · rcases ha with ⟨a, rfl⟩ | rfl
    · have hden := halpha.denote_eq
        (M := alphaUnitEmptyModel) (rho := alphaUnitRho)
      simp only [alphaUnitEmptyModel, alphaBlocked, denote_ex,
        Function.update_eq_self, denote_app, Model.app, pairArgs,
        Fin.forall_fin_two, denote_var, alphaUnitRho, Fin.isValue,
        Set.mem_singleton_iff, and_self, Set.mem_empty_iff_false, and_false,
        exists_const, Set.ofPred_false, Set.iUnion_empty,
        Set.iUnion_singleton_eq_range, Set.range_id'] at hden
      have hmem := Set.ext_iff.mp hden ()
      simp at hmem
    · have hden := halpha.denote_eq
        (M := alphaUnitFullModel) (rho := alphaUnitRho)
      simp [alphaBlocked, alphaUnitFullModel, Model.app, pairArgs,
        alphaUnitRho] at hden

/-- No proof-theoretic alpha variant of `alphaBlocked` has a fresh usable
witness in the pointed binary model. -/
theorem alphaWitnessTheory_not_alphaFreshWitnessed :
    ¬ AlphaFreshWitnessed alphaWitnessTheory := by
  intro hFresh
  obtain ⟨x', p', y, halpha, hyFresh, hyImp⟩ := hFresh alphaBlocked_mem
  obtain ⟨a, b, hp', hax, hb⟩ := alphaBlocked_alphaEq_body_shape halpha
  subst a
  subst b
  subst p'
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    apply hyFresh
    simp [Pattern.allVars, pairArgs]
  have he' : Pattern.ex x'
      (.app AlphaWitnessSym.pair (pairArgs (.var x') (.var 0))) ∈
        alphaWitnessTheory :=
    (alphaWitnessTheory_isMCS.alphaEq_mem_iff halpha).mp alphaBlocked_mem
  change true ∈ alphaWitnessModel.denote alphaWitnessRho
    (.imp (.ex x' (.app .pair (pairArgs (.var x') (.var 0))))
      (Pattern.captureAvoidingSubst x' y
        (.app .pair (pairArgs (.var x') (.var 0))))) at hyImp
  simp only [denote_imp, Set.mem_union, Set.mem_compl_iff] at hyImp
  rcases hyImp with hnot | hinstance
  · exact hnot he'
  · by_cases hx0 : x' = 0
    · subst x'
      simp [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar,
        alphaWitnessModel, Model.app, pairArgs, alphaWitnessRho, hy0] at hinstance
      aesop
    · simp [Pattern.captureAvoidingSubst, Pattern.avoidBinder, substVar,
        alphaWitnessModel, Model.app, pairArgs, alphaWitnessRho, hy0,
        Ne.symm hx0] at hinstance
      aesop

/-- Concrete MCS counterexample to the alpha-relaxed collapse. -/
theorem witnessed_alphaFreshWitnessed_of_isMCS_counterexample :
    ∃ Gamma : Set (Pattern AlphaWitnessSig Nat),
      IsMCS Gamma ∧ Witnessed Gamma ∧ ¬ AlphaFreshWitnessed Gamma := by
  exact ⟨alphaWitnessTheory, alphaWitnessTheory_isMCS,
    alphaWitnessTheory_witnessed,
    alphaWitnessTheory_not_alphaFreshWitnessed⟩

/-- The proposed implication is false, even with the broad proof-theoretic
definition of `Pattern.AlphaEq`. -/
theorem witnessed_alphaFreshWitnessed_of_isMCS_refuted :
    ¬ (∀ {Gamma : Set (Pattern AlphaWitnessSig Nat)},
      IsMCS Gamma → Witnessed Gamma → AlphaFreshWitnessed Gamma) := by
  intro hCollapse
  exact alphaWitnessTheory_not_alphaFreshWitnessed
    (hCollapse alphaWitnessTheory_isMCS alphaWitnessTheory_witnessed)

end

end MatchingLogic
