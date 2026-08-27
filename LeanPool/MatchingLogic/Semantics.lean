/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Free variables, closed patterns, and the three consequence relations
(arXiv:2608.13306v1, Section 2, Definition 1).

Definitions are written by the coordinating session from the paper; the statements below were pinned
before any proof was attempted.
-/
import LeanPool.MatchingLogic.Core

/-!
# MatchingLogic.Semantics
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- The free variables of a pattern.  `∃x` binds `x`. -/
def FV : Pattern S Var → Set Var
  | .var x => {x}
  | .bot => ∅
  | .app _ f => ⋃ i, FV (f i)
  | .imp φ ψ => FV φ ∪ FV ψ
  | .ex x φ => FV φ \ {x}

/-- A pattern is closed when it has no free variables.  The paper assumes
throughout Sections 3-5 that `Γ` and `φ` are closed, without loss of
generality. -/
def Closed (φ : Pattern S Var) : Prop := FV φ = ∅

omit [DecidableEq Var] in
@[simp] theorem FV_var (x : Var) : FV (.var x : Pattern S Var) = {x} := rfl
omit [DecidableEq Var] in
@[simp] theorem FV_bot : FV (.bot : Pattern S Var) = ∅ := rfl
omit [DecidableEq Var] in
@[simp] theorem FV_imp (φ ψ : Pattern S Var) : FV (.imp φ ψ) = FV φ ∪ FV ψ := rfl
omit [DecidableEq Var] in
@[simp] theorem FV_app (σ : S.Sym) (f : Fin (S.arity σ) → Pattern S Var) :
    FV (.app σ f) = ⋃ i, FV (f i) := rfl
omit [DecidableEq Var] in
@[simp] theorem FV_ex (x : Var) (φ : Pattern S Var) : FV (.ex x φ) = FV φ \ {x} := rfl

private theorem denote_congr_induction (M : Model S) (φ : Pattern S Var) :
    ∀ (ρ ρ' : Var → M.carrier), (∀ x ∈ FV φ, ρ x = ρ' x) →
      M.denote ρ φ = M.denote ρ' φ := by
  induction φ with
  | var x =>
    intro ρ ρ' h
    simp only [denote_var]
    rw [h x (by simp)]
  | bot => simp
  | app σ f ih =>
    intro ρ ρ' h
    simp only [denote_app]
    congr 2
    funext i
    exact ih i ρ ρ' (fun x hx => h x (by
      simp only [FV_app, Set.mem_iUnion]
      exact ⟨i, hx⟩))
  | imp φ ψ ihφ ihψ =>
    intro ρ ρ' h
    simp only [denote_imp]
    rw [ihφ ρ ρ' (fun x hx => h x (Set.mem_union_left _ hx)),
        ihψ ρ ρ' (fun x hx => h x (Set.mem_union_right _ hx))]
  | ex x φ ih =>
    intro ρ ρ' h
    simp only [denote_ex]
    congr 1
    funext a
    apply ih (Function.update ρ x a) (Function.update ρ' x a)
    intro y hy
    by_cases hyx : y = x
    · subst y
      simp
    · simp only [Function.update_apply, ite_eq_right hyx]
      exact h y ⟨hy, by simpa using hyx⟩

/-- The denotation depends on a valuation only through the free variables. -/
theorem denote_congr (M : Model S) (φ : Pattern S Var) :
    ∀ (ρ ρ' : Var → M.carrier), (∀ x ∈ FV φ, ρ x = ρ' x) →
      M.denote ρ φ = M.denote ρ' φ :=
  denote_congr_induction M φ

/-- For a closed pattern the denotation does not depend on the valuation at all;
this is what licenses the paper's `⟦ψ⟧` notation. -/
theorem denote_closed (M : Model S) {φ : Pattern S Var} (hφ : Closed φ)
    (ρ ρ' : Var → M.carrier) : M.denote ρ φ = M.denote ρ' φ := by
  apply denote_congr M φ ρ ρ'
  intro x hx
  unfold Closed at hφ
  rw [hφ] at hx
  exact hx.elim

/-! ### Definition 1: totality and the three consequence relations -/

/-- `φ` is total in `M` under `ρ` when `ρ(φ) = M`. -/
def Model.Total (M : Model S) (ρ : Var → M.carrier) (φ : Pattern S Var) : Prop :=
  M.denote ρ φ = Set.univ

/-- `M ⊨ φ`: `φ` is total in `M` under every valuation. -/
def Model.Sat (M : Model S) (φ : Pattern S Var) : Prop := ∀ ρ, M.Total ρ φ

/-- `M ⊨ Γ`. -/
def Model.SatSet (M : Model S) (Γ : Set (Pattern S Var)) : Prop := ∀ γ ∈ Γ, M.Sat γ

/-- `ρ(Δ) = ⋂_{δ ∈ Δ} ρ(δ)`, with value `M` when `Δ = ∅`. -/
def Model.denoteSet (M : Model S) (ρ : Var → M.carrier)
    (Δ : Set (Pattern S Var)) : Set M.carrier :=
  ⋂ δ ∈ Δ, M.denote ρ δ

/-- `Δ ⊨loc φ`: local consequence, comparing denotations pointwise. -/
def LocalCons (Δ : Set (Pattern S Var)) (φ : Pattern S Var) : Prop :=
  ∀ (M : Model S) (ρ : Var → M.carrier), M.denoteSet ρ Δ ⊆ M.denote ρ φ

/-- `Γ ⊨ φ`: global consequence, asking for totality. -/
def GlobalCons (Γ : Set (Pattern S Var)) (φ : Pattern S Var) : Prop :=
  ∀ M : Model S, M.SatSet Γ → M.Sat φ

/-- For closed `φ`, `M ⊨ φ` says exactly `⟦φ⟧ = M`, with no valuation
quantifier left (paper, Section 2, "Closed patterns"). -/
theorem Model.sat_iff_denote_eq_univ (M : Model S) {φ : Pattern S Var}
    (hφ : Closed φ) (ρ : Var → M.carrier) :
    M.Sat φ ↔ M.denote ρ φ = Set.univ := by
  constructor
  · intro hsat
    exact hsat ρ
  · intro hden ρ'
    unfold Model.Total
    rw [denote_closed M hφ ρ' ρ]
    exact hden

end MatchingLogic
