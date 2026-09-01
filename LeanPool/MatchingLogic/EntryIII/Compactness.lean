/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

import LeanPool.MatchingLogic.Semantics
import Mathlib.ModelTheory.Satisfiability

/-!
# MatchingLogic.EntryIII.Compactness
-/

namespace MatchingLogic.EntryIII

open FirstOrder

universe u

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- The relational first-order signature associated to a matching-logic signature.
`sigma` of matching arity `k` becomes a relation of arity `k + 1`; coordinate zero
is the output/current point. -/
def relLanguage (S : Signature) : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := fun n => { sigma : S.Sym // S.arity sigma + 1 = n }

instance relLanguage_isRelational (S : Signature) : (relLanguage S).IsRelational :=
  fun _ => ⟨fun x => nomatch x⟩

/-- The relation symbol associated to a matching symbol. -/
def relSym (sigma : S.Sym) : (relLanguage S).Relations (S.arity sigma + 1) :=
  ⟨sigma, rfl⟩

/-- Relational FOL translation at named free variables `eta` and current point `cur`.
The recursive calls may enlarge the free-variable type with finitely many local
witness variables; `iExs` binds exactly those variables. -/
noncomputable def Pattern.toFOAux :
    (p : Pattern S Var) →
      ∀ {alpha : Type u}, (Var → alpha) → alpha → (relLanguage S).Formula alpha
  | .var x, _, eta, cur =>
      FirstOrder.Language.Term.equal (.var cur) (.var (eta x))
  | .bot, _, _, _ => ⊥
  | .imp phi psi, _, eta, cur =>
      (toFOAux phi eta cur).imp (toFOAux psi eta cur)
  | .ex x phi, alpha, eta, cur =>
      let eta' : Var → alpha ⊕ Unit :=
        Function.update (Sum.inl ∘ eta) x (Sum.inr ())
      (toFOAux phi eta' (Sum.inl cur)).iExs Unit
  | .app sigma args, alpha, eta, cur =>
      let body : (relLanguage S).Formula (alpha ⊕ Fin (S.arity sigma)) :=
        (relSym sigma).formula
            (Fin.cons (.var (Sum.inl cur)) (fun i => .var (Sum.inr i))) ⊓
          FirstOrder.Language.Formula.iInf
            (fun i => toFOAux (args i) (Sum.inl ∘ eta) (Sum.inr i))
      body.iExs (Fin (S.arity sigma))

/-- Translation with free variable `none` for the current point and `some x`
for the matching-logic valuation of `x`. -/
noncomputable def Pattern.toFOFormula (p : Pattern S Var) :
    (relLanguage S).Formula (Option Var) :=
  MatchingLogic.EntryIII.Pattern.toFOAux p some none

/-- Sentence translation. Mathlib's constants extension names the current point
and every matching-logic variable. -/
noncomputable def Pattern.toFOSentence (p : Pattern S Var) :
    (relLanguage S)[[Option Var]].Sentence :=
  FirstOrder.Language.Formula.equivSentence
    (MatchingLogic.EntryIII.Pattern.toFOFormula p)

namespace Model

/-- Interpret the relational FOL signature in a matching-logic model. -/
@[instance_reducible] def toFOStructure (M : Model S) :
    (relLanguage S).Structure M.carrier where
  RelMap := fun {n} r xs =>
    let ys : Fin (S.arity r.1 + 1) → M.carrier := fun i => xs (Fin.cast r.2 i)
    ys 0 ∈ M.interp r.1 (fun i => ys i.succ)

/-- Recover a matching-logic model from a structure in the constants-expanded
relational language. -/
abbrev ofFOStructure (A : Type) [Nonempty A]
    [(relLanguage S)[[Option Var]].Structure A] : Model S where
  carrier := A
  nonempty := inferInstance
  interp sigma args :=
    {out | @FirstOrder.Language.Structure.RelMap
      ((relLanguage S)[[Option Var]]) A inferInstance (S.arity sigma + 1)
      (Sum.inl (relSym sigma)) (Fin.cons out args)}

/-- Valuation recovered from the named constants. -/
def ofFOValuation (A : Type) [(relLanguage S)[[Option Var]].Structure A] : Var → A :=
  fun x => ((relLanguage S).con (some x) : A)

/-- Distinguished current point recovered from the named constant. -/
def ofFOCurrent (A : Type) [(relLanguage S)[[Option Var]].Structure A] : A :=
  ((relLanguage S).con (none : Option Var) : A)

end Model

/-- Correctness of the open-formula translation for any relational structure
whose relation maps agree with a matching-logic model. -/
theorem realize_toFOAux_of_rel (M : Model S) [(relLanguage S).Structure M.carrier]
    (hcompat : ∀ (sigma : S.Sym) (out : M.carrier)
      (args : Fin (S.arity sigma) → M.carrier),
      FirstOrder.Language.Structure.RelMap (relSym sigma) (Fin.cons out args) ↔
        out ∈ M.interp sigma args)
    (p : Pattern S Var) {alpha : Type u}
    (eta : Var → alpha) (cur : alpha) (v : alpha → M.carrier) :
    FirstOrder.Language.Formula.Realize
        (MatchingLogic.EntryIII.Pattern.toFOAux p eta cur) v ↔
      v cur ∈ M.denote (v ∘ eta) p := by
  induction p generalizing alpha with
  | var x => simp [Pattern.toFOAux, Function.comp_def]
  | bot => simp [Pattern.toFOAux]
  | imp phi psi ihphi ihpsi =>
      rw [Pattern.toFOAux, FirstOrder.Language.Formula.realize_imp,
        ihphi eta cur v, ihpsi eta cur v]
      simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
      tauto
  | ex x phi ih =>
      simp only [Pattern.toFOAux, FirstOrder.Language.Formula.realize_iExs,
        denote_ex, Set.mem_iUnion]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w (), ?_⟩
        rw [ih (Function.update (Sum.inl ∘ eta) x (Sum.inr ())) (Sum.inl cur)
          (Sum.elim v w)] at hw
        have heq :
            Sum.elim v w ∘ Function.update (Sum.inl ∘ eta) x (Sum.inr ()) =
              Function.update (v ∘ eta) x (w ()) := by
          funext y
          by_cases hy : y = x
          · subst y
            simp
          · simp [hy, Function.comp_def]
        rwa [heq] at hw
      · rintro ⟨a, ha⟩
        refine ⟨fun _ => a, ?_⟩
        rw [ih (Function.update (Sum.inl ∘ eta) x (Sum.inr ())) (Sum.inl cur)
          (Sum.elim v (fun _ => a))]
        have heq :
            Sum.elim v (fun _ => a) ∘
                Function.update (Sum.inl ∘ eta) x (Sum.inr ()) =
              Function.update (v ∘ eta) x a := by
          funext y
          by_cases hy : y = x
          · subst y
            simp
          · simp [hy, Function.comp_def]
        rwa [heq]
  | app sigma args ih =>
      simp only [Pattern.toFOAux, FirstOrder.Language.Formula.realize_iExs,
        FirstOrder.Language.Formula.realize_inf,
        FirstOrder.Language.Formula.realize_rel,
        FirstOrder.Language.Formula.realize_iInf,
        denote_app, MatchingLogic.Model.app]
      constructor
      · rintro ⟨w, hrel, hargs⟩
        have htuple :
            (fun i => FirstOrder.Language.Term.realize (Sum.elim v w)
              ((Fin.cons (FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inl cur))
                (fun j => FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inr j)) :
                  Fin (S.arity sigma + 1) →
                    (relLanguage S).Term (alpha ⊕ Fin (S.arity sigma))) i)) =
              Fin.cons (v cur) w := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        rw [htuple] at hrel
        refine ⟨w, ?_, ?_⟩
        · intro i
          have hi := hargs i
          rw [ih i (Sum.inl ∘ eta) (Sum.inr i) (Sum.elim v w)] at hi
          simpa [Function.comp_def] using hi
        · exact (hcompat sigma (v cur) w).mp (by simpa using hrel)
      · rintro ⟨w, hargs, hrel⟩
        have htuple :
            (fun i => FirstOrder.Language.Term.realize (Sum.elim v w)
              ((Fin.cons (FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inl cur))
                (fun j => FirstOrder.Language.Term.var (L := relLanguage S) (Sum.inr j)) :
                  Fin (S.arity sigma + 1) →
                    (relLanguage S).Term (alpha ⊕ Fin (S.arity sigma))) i)) =
              Fin.cons (v cur) w := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp
        refine ⟨w, ?_, ?_⟩
        · rw [htuple]
          exact (hcompat sigma (v cur) w).mpr hrel
        · intro i
          rw [ih i (Sum.inl ∘ eta) (Sum.inr i) (Sum.elim v w)]
          simpa [Function.comp_def] using hargs i

/-- Correctness specialized to the FOL structure built from a matching model. -/
theorem realize_toFOAux (M : Model S) (p : Pattern S Var) {alpha : Type u}
    (eta : Var → alpha) (cur : alpha) (v : alpha → M.carrier) :
    @FirstOrder.Language.Formula.Realize (relLanguage S) M.carrier
        (Model.toFOStructure M) alpha
        (MatchingLogic.EntryIII.Pattern.toFOAux p eta cur) v ↔
      v cur ∈ M.denote (v ∘ eta) p := by
  let : (relLanguage S).Structure M.carrier := Model.toFOStructure M
  apply realize_toFOAux_of_rel M
  intro sigma out args
  rfl

/-- A valuation of the FOL parameters from a matching valuation and current point. -/
def Model.toFOParameters (M : Model S) (rho : Var → M.carrier) (u : M.carrier) :
    Option Var → M.carrier
  | none => u
  | some x => rho x

/-- Correctness of sentence translation in the constants expansion built from a
matching model, valuation, and current point. -/
theorem realize_toFOSentence (M : Model S) (rho : Var → M.carrier)
    (u : M.carrier) (p : Pattern S Var) :
    letI : (relLanguage S).Structure M.carrier := Model.toFOStructure M
    letI : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
      FirstOrder.Language.constantsOn.structure
        (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
    M.carrier ⊨ MatchingLogic.EntryIII.Pattern.toFOSentence p ↔
      u ∈ M.denote rho p := by
  let : (relLanguage S).Structure M.carrier := Model.toFOStructure M
  let : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
    FirstOrder.Language.constantsOn.structure
      (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
  unfold MatchingLogic.EntryIII.Pattern.toFOSentence
  rw [FirstOrder.Language.Formula.realize_equivSentence]
  unfold MatchingLogic.EntryIII.Pattern.toFOFormula
  have hv :
      (fun a => ((relLanguage S).con a : M.carrier)) =
        MatchingLogic.EntryIII.Model.toFOParameters M rho u := by
    funext a
    cases a <;> rfl
  rw [hv]
  have h := realize_toFOAux M p some none
    (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
  have hrho :
      MatchingLogic.EntryIII.Model.toFOParameters M rho u ∘ some = rho := by
    funext x
    rfl
  rwa [hrho] at h

/-- Correctness in an arbitrary structure of the constants-expanded language,
after recovering its matching model, valuation, and current point. -/
theorem realize_toFOSentence_ofFOStructure (A : Type) [Nonempty A]
    [(relLanguage S)[[Option Var]].Structure A] (p : Pattern S Var) :
    A ⊨ MatchingLogic.EntryIII.Pattern.toFOSentence p ↔
      Model.ofFOCurrent (S := S) (Var := Var) A ∈
        (Model.ofFOStructure (S := S) (Var := Var) A).denote
          (Model.ofFOValuation (S := S) (Var := Var) A) p := by
  let : (relLanguage S).Structure A :=
    ((relLanguage S).lhomWithConstants (Option Var)).reduct A
  have : ((relLanguage S).lhomWithConstants (Option Var)).IsExpansionOn A :=
    inferInstance
  unfold MatchingLogic.EntryIII.Pattern.toFOSentence
  rw [FirstOrder.Language.Formula.realize_equivSentence]
  unfold MatchingLogic.EntryIII.Pattern.toFOFormula
  rw [realize_toFOAux_of_rel
    (Model.ofFOStructure (S := S) (Var := Var) A)]
  · rfl
  · intro sigma out args
    rfl

/-- The first-order theory describing a counterexample to `Delta ⊨loc phi`. -/
noncomputable def counterTheory (Delta : Set (Pattern S Var)) (phi : Pattern S Var) :
    (relLanguage S)[[Option Var]].Theory :=
  MatchingLogic.EntryIII.Pattern.toFOSentence '' Delta ∪
    {(MatchingLogic.EntryIII.Pattern.toFOSentence phi).not}

/-- A local semantic consequence has no FOL countermodel under the translation. -/
theorem not_counterTheory_isSatisfiable {Delta : Set (Pattern S Var)}
    {phi : Pattern S Var} (hlocal : LocalCons Delta phi) :
    ¬ FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by
  intro hsat
  let A := hsat.some
  let M : Model S := Model.ofFOStructure (S := S) (Var := Var) A
  let rho : Var → M.carrier := Model.ofFOValuation (S := S) (Var := Var) A
  let u : M.carrier := Model.ofFOCurrent (S := S) (Var := Var) A
  have hDelta : u ∈ M.denoteSet rho Delta := by
    simp only [MatchingLogic.Model.denoteSet, Set.mem_iInter]
    intro delta hdelta
    apply (realize_toFOSentence_ofFOStructure (S := S) (Var := Var) A delta).mp
    exact (counterTheory Delta phi).realize_sentence_of_mem
      (Set.mem_union_left _ ⟨delta, hdelta, rfl⟩)
  have hphi : u ∈ M.denote rho phi := hlocal M rho hDelta
  have hnphi : ¬ u ∈ M.denote rho phi := by
    intro hu
    have hsent :=
      (realize_toFOSentence_ofFOStructure (S := S) (Var := Var) A phi).mpr hu
    have hnSent : A ⊨ (MatchingLogic.EntryIII.Pattern.toFOSentence phi).not :=
      (counterTheory Delta phi).realize_sentence_of_mem
        (Set.mem_union_right _ (Set.mem_singleton _))
    exact ((FirstOrder.Language.Sentence.realize_not A).mp hnSent) hsent
  exact hnphi hphi

/-- Conversely, a matching counterexample yields a model of the FOL
counterexample theory. -/
theorem counterTheory_isSatisfiable_of_counterexample
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (M : Model S) (rho : Var → M.carrier) (u : M.carrier)
    (hDelta : u ∈ M.denoteSet rho Delta) (hphi : u ∉ M.denote rho phi) :
    FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by
  let : (relLanguage S).Structure M.carrier := Model.toFOStructure M
  let : (FirstOrder.Language.constantsOn (Option Var)).Structure M.carrier :=
    FirstOrder.Language.constantsOn.structure
      (MatchingLogic.EntryIII.Model.toFOParameters M rho u)
  have hmodel : M.carrier ⊨ counterTheory Delta phi := by
    rw [FirstOrder.Language.Theory.model_iff]
    intro theta htheta
    rcases htheta with htheta | htheta
    · rcases htheta with ⟨delta, hdelta, rfl⟩
      apply (realize_toFOSentence M rho u delta).mpr
      have hDelta' := hDelta
      simp only [MatchingLogic.Model.denoteSet, Set.mem_iInter] at hDelta'
      exact hDelta' delta hdelta
    · rw [Set.mem_singleton_iff] at htheta
      subst theta
      rw [FirstOrder.Language.Sentence.realize_not]
      intro hsent
      exact hphi ((realize_toFOSentence M rho u phi).mp hsent)
  let : M.carrier ⊨ counterTheory Delta phi := hmodel
  exact FirstOrder.Language.Theory.Model.isSatisfiable M.carrier

/-- Exact semantic equivalence used by the compactness reduction. -/
theorem localCons_iff_not_counterTheory_isSatisfiable
    {Delta : Set (Pattern S Var)} {phi : Pattern S Var} :
    LocalCons Delta phi ↔
      ¬ FirstOrder.Language.Theory.IsSatisfiable (counterTheory Delta phi) := by
  refine ⟨not_counterTheory_isSatisfiable, ?_⟩
  intro hunsat M rho u hu
  by_contra hphi
  exact hunsat (counterTheory_isSatisfiable_of_counterexample M rho u hu hphi)

/-- **Semantic local compactness for matching logic.**  No countability
assumption is needed on the matching-symbol type or on the variable type. -/
theorem localCons_compact {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hlocal : LocalCons Delta phi) :
    ∃ l : List (Pattern S Var),
      (∀ delta ∈ l, delta ∈ Delta) ∧
        LocalCons {delta | delta ∈ l} phi := by
  classical
  let Piece : Option {delta // delta ∈ Delta} →
      (relLanguage S)[[Option Var]].Theory
    | none => {(MatchingLogic.EntryIII.Pattern.toFOSentence phi).not}
    | some delta => {MatchingLogic.EntryIII.Pattern.toFOSentence delta.1}
  have hcounter : counterTheory Delta phi = ⋃ i, Piece i := by
    ext theta
    constructor
    · intro htheta
      rcases htheta with htheta | htheta
      · rcases htheta with ⟨delta, hdelta, rfl⟩
        apply Set.mem_iUnion.mpr
        refine ⟨some ⟨delta, hdelta⟩, ?_⟩
        simp [Piece]
      · apply Set.mem_iUnion.mpr
        refine ⟨none, ?_⟩
        simpa [Piece] using htheta
    · intro htheta
      rcases Set.mem_iUnion.mp htheta with ⟨i, hi⟩
      cases i with
      | none =>
          exact Set.mem_union_right _ (by simpa [Piece] using hi)
      | some delta =>
          apply Set.mem_union_left
          have heq : theta = MatchingLogic.EntryIII.Pattern.toFOSentence delta.1 := by
            simpa [Piece] using hi
          exact ⟨delta.1, delta.2, heq.symm⟩
  have hUnionUnsat : ¬ FirstOrder.Language.Theory.IsSatisfiable (⋃ i, Piece i) := by
    rw [← hcounter]
    exact (localCons_iff_not_counterTheory_isSatisfiable.mp hlocal)
  have hNotAll :
      ¬ ∀ s : Finset (Option {delta // delta ∈ Delta}),
        FirstOrder.Language.Theory.IsSatisfiable (⋃ i ∈ s, Piece i) := by
    intro hall
    exact hUnionUnsat
      ((FirstOrder.Language.Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset Piece).mpr
        hall)
  push Not at hNotAll
  obtain ⟨s, hs⟩ := hNotAll
  let l : List (Pattern S Var) :=
    s.toList.filterMap (fun
      | none => none
      | some delta => some delta.1)
  refine ⟨l, ?_, ?_⟩
  · intro delta hdelta
    simp only [l, List.mem_filterMap] at hdelta
    obtain ⟨i, hi, himap⟩ := hdelta
    cases i with
    | none => simp at himap
    | some d =>
        simp only [Option.some.injEq] at himap
        subst delta
        exact d.2
  · apply localCons_iff_not_counterTheory_isSatisfiable.mpr
    intro hbig
    apply hs
    apply hbig.mono
    intro theta htheta
    rcases Set.mem_iUnion.mp htheta with ⟨i, htheta⟩
    rcases Set.mem_iUnion.mp htheta with ⟨hi, hpiece⟩
    cases i with
    | none =>
        exact Set.mem_union_right _ (by simpa [Piece] using hpiece)
    | some d =>
        apply Set.mem_union_left
        have hdlist : d.1 ∈ l := by
          simp only [l, List.mem_filterMap]
          exact ⟨some d, by simpa using hi, rfl⟩
        have heq : theta = MatchingLogic.EntryIII.Pattern.toFOSentence d.1 := by
          simpa [Piece] using hpiece
        exact ⟨d.1, hdlist, heq.symm⟩

end MatchingLogic.EntryIII

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- Public form of semantic local compactness, used to reduce arbitrary
signatures to the finite symbol support of finitely many premises and the
conclusion. -/
theorem localCons_compact {Delta : Set (Pattern S Var)} {phi : Pattern S Var}
    (hlocal : LocalCons Delta phi) :
    ∃ l : List (Pattern S Var),
      (∀ delta ∈ l, delta ∈ Delta) ∧
        LocalCons {delta | delta ∈ l} phi :=
  EntryIII.localCons_compact hlocal

end MatchingLogic
