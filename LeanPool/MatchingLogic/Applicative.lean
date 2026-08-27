/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Applicative matching logic — arXiv:2608.13306v1, Section 6.

The paper:

  "Applicative matching logic is the instance in which Σ consists of one binary
   symbol, application, written by juxtaposition, together with any set of
   constants.  It has two coordinates, which we write 1 and 2, and the boxes of
   Definition 3 become

       [1]ψ = ((ψ → ⊥)⊤) → ⊥,   [2]ψ = (⊤(ψ → ⊥)) → ⊥,

   with a·b ⇝₁ a and a·b ⇝₂ b, and E* = {1,2}*.  Everything above applies
   unchanged, so Corollary 15 holds for applicative matching logic."

Every clause of that paragraph is a checkable claim about the general
development, and this file checks them.  Nothing here is new mathematics; the
point is that the instantiation really is an instantiation, and that the
explicit box formulas the paper writes down really are the general `box` at
those two coordinates.

Statements pinned before any proof was attempted.
-/
import Mathlib.Data.Fin.VecNotation
import LeanPool.MatchingLogic.Composite

/-!
# MatchingLogic.Applicative
-/

namespace MatchingLogic
namespace Applicative

variable {Const : Type} {Var : Type} [DecidableEq Var]

/-- The applicative signature: one binary symbol together with a set of
constants. -/
abbrev appSig (Const : Type) : Signature :=
  ⟨Option Const, fun s => match s with | none => 2 | some _ => 0⟩

/-- Application. -/
abbrev appSym : (appSig Const).Sym := none

/-- The first coordinate, the paper's `1`. -/
abbrev coord₁ : Coord (appSig Const) := ⟨none, 0⟩
/-- The second coordinate, the paper's `2`. -/
abbrev coord₂ : Coord (appSig Const) := ⟨none, 1⟩

/-- Juxtaposition: `φ ψ`. -/
abbrev ap (φ ψ : Pattern (appSig Const) Var) : Pattern (appSig Const) Var :=
  .app appSym ![φ, ψ]

private theorem fin_two_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  omega

/-- **"It has two coordinates."**  A constant contributes none, and the binary
symbol contributes exactly two. -/
theorem coord_eq (e : Coord (appSig Const)) : e = coord₁ ∨ e = coord₂ := by
  rcases e with ⟨s, i⟩
  cases s with
  | none =>
      change Fin 2 at i
      rcases fin_two_cases i with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  | some c =>
      exact Fin.elim0 i

omit [DecidableEq Var] in
/-- **`[1]ψ = ((ψ → ⊥)⊤) → ⊥`**, verbatim from the paper. -/
theorem box_coord₁ (ψ : Pattern (appSig Const) Var) :
    box coord₁ ψ = .imp (ap (.imp ψ .bot) Pattern.tp) .bot := by
  unfold box dia ap
  congr 2
  funext i
  change Fin 2 at i
  rcases fin_two_cases i with rfl | rfl <;> rfl

omit [DecidableEq Var] in
/-- **`[2]ψ = (⊤(ψ → ⊥)) → ⊥`**, verbatim from the paper. -/
theorem box_coord₂ (ψ : Pattern (appSig Const) Var) :
    box coord₂ ψ = .imp (ap Pattern.tp (.imp ψ .bot)) .bot := by
  unfold box dia ap
  congr 2
  funext i
  change Fin 2 at i
  rcases fin_two_cases i with rfl | rfl <;> rfl

/-- **`a·b ⇝₁ a`.** -/
theorem stepAt_coord₁ (M : Model (appSig Const)) (u v : M.carrier) :
    M.stepAt coord₁ u v ↔ ∃ a b : M.carrier, u ∈ M.interp appSym ![a, b] ∧ v = a := by
  change (∃ ab : Fin 2 → M.carrier, u ∈ M.interp none ab ∧ v = ab 0) ↔
    ∃ a b : M.carrier, u ∈ M.interp none ![a, b] ∧ v = a
  constructor
  · rintro ⟨ab, hab, hv⟩
    refine ⟨ab 0, ab 1, ?_, hv⟩
    rw [show ![ab 0, ab 1] = ab by
      funext i
      rcases fin_two_cases i with rfl | rfl <;> rfl]
    exact hab
  · rintro ⟨a, b, hab, hv⟩
    refine ⟨![a, b], hab, ?_⟩
    exact hv

/-- **`a·b ⇝₂ b`.** -/
theorem stepAt_coord₂ (M : Model (appSig Const)) (u v : M.carrier) :
    M.stepAt coord₂ u v ↔ ∃ a b : M.carrier, u ∈ M.interp appSym ![a, b] ∧ v = b := by
  change (∃ ab : Fin 2 → M.carrier, u ∈ M.interp none ab ∧ v = ab 1) ↔
    ∃ a b : M.carrier, u ∈ M.interp none ![a, b] ∧ v = b
  constructor
  · rintro ⟨ab, hab, hv⟩
    refine ⟨ab 0, ab 1, ?_, hv⟩
    rw [show ![ab 0, ab 1] = ab by
      funext i
      rcases fin_two_cases i with rfl | rfl <;> rfl]
    exact hab
  · rintro ⟨a, b, hab, hv⟩
    refine ⟨![a, b], hab, ?_⟩
    exact hv

/-- **"Everything above applies unchanged."**  Theorem 13 for applicative
matching logic, by instantiation and nothing else. -/
theorem semantic_localization_applicative
    {Γ : Set (Pattern (appSig Const) Var)} {φ : Pattern (appSig Const) Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) :
    GlobalCons Γ φ ↔ LocalCons (localize Γ) φ := by
  exact semantic_localization hΓ hφ

end Applicative
end MatchingLogic
