/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Written by the coordinating session: adversarial check on Lemma 9 (2026-08-25).

A mechanized lemma is worth only what it forbids.  `locality` carries a
backward-closure hypothesis; if the conclusion held without it, our encoding of
the pointwise extension would be too weak and the mechanization would be
vacuous where it matters.  This file exhibits a model, a set `C` that is NOT
backward closed, and two valuations satisfying `AgreeOn C` whose denotations
differ on `C`.  So the hypothesis is load-bearing.

The example is the smallest one that works: `M \ C` must have two points, since
`AgreeOn` forces the two valuations to agree whenever their common value lies
in `C`, and a one-point complement leaves them equal.
-/
import LeanPool.MatchingLogic.Locality

/-!
# MatchingLogic.Necessity
-/

namespace MatchingLogic
namespace Necessity

/-- One unary symbol. -/
abbrev S : Signature := ⟨Unit, fun _ => 1⟩

/-- Carrier `{0,1,2}`; the symbol sends `1` to `0` and everything else nowhere.
Since `0 ∈ σ_M(1)`, the backward step of Definition 2 runs from the output to the
argument: `0 ⇝ 1`.  So backward closure of `{0}` would force `1 ∈ {0}`. -/
abbrev M : Model S :=
  { carrier := Fin 3
    nonempty := ⟨0⟩
    interp := fun _ a => if a 0 = 1 then ({0} : Set (Fin 3)) else ∅ }

/-- The set `{0}`, which is not backward closed. -/
abbrev C : Set (Fin 3) := {0}

theorem C_not_backwardClosed : ¬ M.BackwardClosed C := by
  intro h
  have h1 : (1 : Fin 3) ∈ C := h (show (0 : Fin 3) ∈ C from rfl) ⟨(), fun _ => 1, 0, by simp, rfl⟩
  exact absurd h1 (by decide)

/-! The countermodel is stated for an arbitrary variable type, then instantiated
both at `Unit` and at `ℕ`.  The `ℕ` instance is the paper's setting, where the
element variables are countably infinite, so this refutes the hypothesis-free
statement in the paper's own domain and not merely in a degenerate one. -/

section Generic

variable {Var : Type} [DecidableEq Var]

/-- `σ(x)` for a chosen variable `x`. -/
def psi (x : Var) : Pattern S Var := .app () (fun _ => .var x)

/-- Both valuations send every variable outside `C`, so they satisfy `AgreeOn`. -/
def rho : Var → Fin 3 := fun _ => 1
/-- The second constant valuation used by the agreement counterexample. -/
def rho' : Var → Fin 3 := fun _ => 2

omit [DecidableEq Var] in
theorem agree : AgreeOn (M := M) C (rho (Var := Var)) rho' := by
  intro _
  refine Or.inr ⟨?_, ?_⟩ <;> simp [rho, rho']

theorem denote_rho (x : Var) : M.denote (rho (Var := Var)) (psi x) = {0} := by
  ext u
  simp only [psi, denote_app, Model.app, denote_var, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hu⟩
    have h0 : a 0 = 1 := ha 0
    simpa [h0] using hu
  · intro hu
    exact ⟨fun _ => 1, fun _ => rfl, by simpa using hu⟩

theorem denote_rho' (x : Var) : M.denote (rho' (Var := Var)) (psi x) = ∅ := by
  ext u
  simp only [psi, denote_app, Model.app, denote_var, Set.mem_ofPred_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, hu⟩
  have h0 : a 0 = 2 := ha 0
  simp [h0] at hu

/-- **The hypothesis of Lemma 9 cannot be dropped**, for any variable type that
has at least one variable.  Without backward closure the conclusion fails, on a
three-element model. -/
theorem locality_needs_backwardClosed (x : Var) :
    ¬ (∀ (ψ : Pattern S Var) (ρ ρ' : Var → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) := by
  intro h
  have hd := h (psi x) rho rho' agree
  rw [denote_rho, denote_rho'] at hd
  have h0 : (0 : Fin 3) ∈ ({0} : Set (Fin 3)) ∩ C := ⟨rfl, rfl⟩
  rw [hd] at h0
  exact h0.1

end Generic

/-- The paper's setting: countably infinite element variables. -/
theorem locality_needs_backwardClosed_nat :
    ¬ (∀ (ψ : Pattern S Nat) (ρ ρ' : Nat → Fin 3),
        AgreeOn (M := M) C ρ ρ' → M.denote ρ ψ ∩ C = M.denote ρ' ψ ∩ C) :=
  locality_needs_backwardClosed 0

end Necessity
end MatchingLogic
