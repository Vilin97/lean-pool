/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Written by the coordinating session: controls on `Core.lean` (2026-08-25).
These are not part of the paper; they exist so that a wrong definition cannot
pass unnoticed. Each one
would FAIL if the corresponding clause of Section 2 were mis-encoded.
-/
import LeanPool.MatchingLogic.Core

/-!
# MatchingLogic.Sanity
-/

namespace MatchingLogic
namespace Model

variable {S : Signature}

/-- Control 1: the pointwise extension is `∅` as soon as one argument is
(paper, Section 2, sentence after the display).  This would fail if `app` used
`∀ i, a i ∈ A i` with an existential over a *partial* tuple, or if it forgot the
tuple entirely. -/
theorem app_eq_empty (M : Model S) (σ : S.Sym)
    (A : Fin (S.arity σ) → Set M.carrier) (i : Fin (S.arity σ)) (h : A i = ∅) :
    M.app σ A = ∅ := by
  ext u
  simp only [app, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, -⟩
  have := ha i
  rw [h] at this
  exact this

/-- Control 2: a constant is interpreted by a subset of the carrier, and its
denotation does not depend on the valuation.  `Fin 0` being empty is what makes
the tuple unique. -/
theorem app_const (M : Model S) (σ : S.Sym) (h : S.arity σ = 0)
    (A : Fin (S.arity σ) → Set M.carrier) :
    M.app σ A = M.interp σ (fun i => absurd i.isLt (by omega)) := by
  ext u
  simp only [app, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, -, hu⟩
    have : a = fun i => absurd i.isLt (by omega : ¬ (i.val < S.arity σ)) := by
      funext i; exact absurd i.isLt (by omega)
    rwa [this] at hu
  · intro hu
    exact ⟨_, fun i => absurd i.isLt (by omega), hu⟩

/-- Control 3: the definitions are not vacuous.  In the signature with one unary
symbol interpreted as the full set, over a two-element carrier, the singleton
`{true}` is NOT backward closed -- so `BackwardClosed` is a real restriction and
Lemma 9's hypothesis is not free. -/
example :
    let S : Signature := ⟨Unit, fun _ => 1⟩
    let M : Model S := ⟨Bool, ⟨true⟩, fun _ _ => Set.univ⟩
    ¬ M.BackwardClosed {true} := by
  intro S M h
  have : (false : Bool) ∈ ({true} : Set Bool) :=
    h (by rfl) ⟨(), fun _ => false, ⟨0, Nat.zero_lt_one⟩, trivial, rfl⟩
  simp at this

end Model
end MatchingLogic
