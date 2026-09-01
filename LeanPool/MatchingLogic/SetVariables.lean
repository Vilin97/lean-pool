/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Remark 17 — free set variables do not come along. arXiv:2608.13306v1, Section 5.

  "One might expect Corollary 15 to extend to patterns with free set variables,
   by reading such a variable as a constant. This extension fails under the
   consequence relation of Definition 1. Satisfaction quantifies over all
   valuations, so a free set variable is quantified INSIDE the premise, whereas
   a constant is fixed by the model. Thus the two are not interchangeable. Take
   Γ = {X} and φ = ⊥. No model satisfies X, since the valuation sending X to ∅
   makes it not total, so Γ ⊨ ⊥ holds vacuously. Replacing X by a fresh constant
   d gives {d} ⊭ ⊥, as the model with d_M = M shows."

This file mechanizes that counterexample, and so marks the boundary of
Corollary 15: it does not extend to free set variables.

The base development stays free of set variables — `Core.lean` is untouched.
The extended syntax lives here and nowhere else, exactly as `Definedness.lean`
keeps definedness out of the base language.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.EntryPoints

/-!
# MatchingLogic.SetVariables
-/

namespace MatchingLogic
namespace SetVariables

variable {S : Signature} {Var SVar : Type} [DecidableEq Var]

/-- Patterns extended with free set variables.  There is no `μ` and no binder
for set variables: the point of Remark 17 concerns FREE set variables only. -/
inductive SPattern (S : Signature) (Var SVar : Type) where
  | var : Var → SPattern S Var SVar
  | svar : SVar → SPattern S Var SVar
  | app : (σ : S.Sym) → (Fin (S.arity σ) → SPattern S Var SVar) → SPattern S Var SVar
  | imp : SPattern S Var SVar → SPattern S Var SVar → SPattern S Var SVar
  | bot : SPattern S Var SVar
  | ex : Var → SPattern S Var SVar → SPattern S Var SVar

/-- A valuation now sends element variables to points and set variables to
arbitrary subsets. -/
structure SVal (M : Model S) (Var SVar : Type) where
  /-- The valuation of element variables. -/
  elem : Var → M.carrier
  /-- The valuation of set variables. -/
  sets : SVar → Set M.carrier

/-- The denotation, extending Section 2 with the clause `ρ(X) = ρ(X)`. -/
def sdenote (M : Model S) : SVal M Var SVar → SPattern S Var SVar → Set M.carrier
  | ρ, .var x => {ρ.elem x}
  | ρ, .svar X => ρ.sets X
  | _, .bot => ∅
  | ρ, .app σ f => M.app σ (fun i => sdenote M ρ (f i))
  | ρ, .imp a b => (sdenote M ρ a)ᶜ ∪ sdenote M ρ b
  | ρ, .ex x a => ⋃ v : M.carrier, sdenote M ⟨Function.update ρ.elem x v, ρ.sets⟩ a

/-- `M ⊨ φ`, with the valuation quantifier ranging over set valuations too --
which is exactly what makes a free set variable behave unlike a constant. -/
def SSat (M : Model S) (φ : SPattern S Var SVar) : Prop :=
  ∀ ρ : SVal M Var SVar, sdenote M ρ φ = Set.univ

/-- `Γ ⊨ φ` in the extended language. -/
def SGlobalCons (Γ : Set (SPattern S Var SVar)) (φ : SPattern S Var SVar) : Prop :=
  ∀ M : Model S, (∀ γ ∈ Γ, SSat M γ) → SSat M φ

/-! ### The two halves of the counterexample -/

/-- **No model satisfies a bare set variable**, because the valuation sending it
to `∅` makes it not total.  This is the step a constant does not admit. -/
theorem not_ssat_svar (M : Model S) (X : SVar) :
    ¬ SSat (Var := Var) M (.svar X) := by
  intro h
  let a : M.carrier := Classical.choice M.nonempty
  let ρ : SVal M Var SVar := ⟨fun _ => a, fun _ => ∅⟩
  have hρ := h ρ
  change (∅ : Set M.carrier) = Set.univ at hρ
  exact Set.empty_ne_univ hρ

/-- Hence `{X} ⊨ ⊥` holds **vacuously**. -/
theorem sGlobalCons_svar_bot (X : SVar) :
    SGlobalCons (S := S) (Var := Var) {SPattern.svar X} SPattern.bot := by
  intro M hM
  exact (not_ssat_svar M X (hM (.svar X) (by simp))).elim

/-- The signature with a single constant `d`. -/
abbrev constSig : Signature := ⟨Unit, fun _ => 0⟩

/-- `d` itself, as a pattern of the base language. -/
abbrev dPat : Pattern constSig Var := .app () (fun i => i.elim0)

/-- A one-point model in which the constant `d` denotes the whole carrier. -/
abbrev fullConstModel : Model constSig :=
  ⟨Unit, ⟨()⟩, fun _ _ => Set.univ⟩

/-- **But `{d} ⊭ ⊥`**, as the model with `d_M = M` shows.  So replacing the set
variable by a constant changes the truth of the consequence. -/
theorem not_globalCons_const_bot :
    ¬ GlobalCons (S := constSig) (Var := Var) {dPat} Pattern.bot := by
  intro h
  have hd : fullConstModel.SatSet ({dPat} : Set (Pattern constSig Var)) := by
    intro φ hφ ρ
    have : φ = dPat := by simpa using hφ
    subst φ
    unfold Model.Total
    ext u
    simp [Model.denote, Model.app]
  have hbot := h fullConstModel hd (fun _ => ())
  unfold Model.Total at hbot
  exact Set.empty_ne_univ hbot

/-- **Remark 17.**  Reading a free set variable as a constant does not preserve
global consequence: the same `Γ ⊨ φ` is true on the left and false on the right.
So Corollary 15 does not extend to patterns with free set variables. -/
theorem set_variable_is_not_a_constant (X : SVar) :
    SGlobalCons (S := constSig) (Var := Var) {SPattern.svar X} SPattern.bot ∧
      ¬ GlobalCons (S := constSig) (Var := Var) {dPat} Pattern.bot := by
  exact ⟨sGlobalCons_svar_bot X, not_globalCons_const_bot⟩

end SetVariables
end MatchingLogic
