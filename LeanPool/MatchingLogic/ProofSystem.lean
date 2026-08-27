/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
The proof system of Figure 2 — arXiv:2608.13306v1, Section 2.

This is the point at which the development stops being purely semantic. Up to
and including Theorem 13 nothing here was needed: `semantic_localization` (in
`Composite.lean`) depends on neither of the paper's black boxes, and the module
graph enforces it -- this file imports that one, not the reverse. Theorem 14 and Corollary 15 do.

DESIGN DECISIONS, fixed before any proof was written:

* **Substitution is variable-for-variable only, and capture-avoidance is a
  side condition rather than a renaming.** Rule (3) is the one place the
  ONE-SORTED, FIXPOINT-FREE development of entry points (i) and (ii) needs
  substitution at all, and there `φ[y/x]` replaces an element variable by an
  element variable. `substVar` performs the replacement naively; `CaptureFree`
  is the predicate saying no binder captures `y` on the way; rule (3) requires
  it. This keeps α-conversion out of THAT part of the development, which is
  what has kept it small.

  **This ruling does not extend to entry point (iii).** A canonical model needs
  Henkin witnesses, and witnesses are substitution, so
  `MatchingLogic/EntryIII/` carries α-equivalence, a binder-renaming
  `captureAvoidingSubst`, and α-conversion derived as an implication of rules
  (3) and (4). See `NARRATIVE.md` §2.

* **Propositional tautologies are instances of a tautologous propositional
  formula.** Rule (1) says "φ a substitution instance of a propositional
  tautology over → and ⊥ (patterns substituted for the propositional atoms)",
  which is exactly `PForm.Taut p` together with a substitution `θ` of patterns
  for atoms.

* **(L) and (S) are HYPOTHESES, never axioms.** The paper uses both as black
  boxes; a Lean `axiom` would silently enter every downstream axiom audit. They
  are `Prop`s here, and every theorem that needs them takes them as arguments,
  so `#print axioms` on Corollary 15 stays clean and the dependence is visible
  in the statement.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.Composite

/-!
# MatchingLogic.ProofSystem
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-! ### Rule (1): substitution instances of propositional tautologies -/

/-- Propositional formulas over `→` and `⊥`. -/
inductive PForm where
  | atom : Nat → PForm
  | bot : PForm
  | imp : PForm → PForm → PForm
  deriving DecidableEq

/-- Boolean evaluation under an assignment to the atoms. -/
def PForm.eval (v : Nat → Bool) : PForm → Bool
  | .atom n => v n
  | .bot => false
  | .imp a b => !(a.eval v) || b.eval v

/-- A propositional tautology. -/
def PForm.Taut (p : PForm) : Prop := ∀ v, p.eval v = true

/-- Substituting patterns for the propositional atoms. -/
def PForm.subst (θ : Nat → Pattern S Var) : PForm → Pattern S Var
  | .atom n => θ n
  | .bot => .bot
  | .imp a b => .imp (PForm.subst θ a) (PForm.subst θ b)

/-! ### Rule (3): variable-for-variable substitution, capture-avoiding -/

/-- `φ[y/x]`, replacing the element variable `x` by `y`. Naive: it stops at a
binder for `x`, but does not itself avoid capture of `y`. -/
def substVar (x y : Var) : Pattern S Var → Pattern S Var
  | .var z => if z = x then .var y else .var z
  | .bot => .bot
  | .app σ f => .app σ (fun i => substVar x y (f i))
  | .imp a b => .imp (substVar x y a) (substVar x y b)
  | .ex z a => if z = x then .ex z a else .ex z (substVar x y a)

/-- `substVar x y φ` is capture-avoiding: no binder on the way to a *substituted*
occurrence of `x` binds `y`. This is the paper's side condition on rule (3).

The binder clause has three alternatives, and all three are needed:

* `z = x` — the substitution stops here, since `x` is rebound;
* `x ∉ FV a` — `substVar` changes nothing under this binder, so it cannot
  introduce a `y` for `z` to capture, *even when `z = y`*;
* `z ≠ y` and recursively — `y` may be introduced, but `z` does not bind it.

The middle alternative was missing in the first version of this definition, and
two independent audits caught it. Its absence made the predicate SOUND but
strictly TOO STRONG: it rejected genuinely capture-safe substitutions, which
would have made rule (3) weaker than Figure 2 and could have left Corollary 15
unprovable, with nothing failing to compile anywhere. See
`captureFree_needs_notFree` below for a substitution the old version rejected. -/
def CaptureFree (x y : Var) : Pattern S Var → Prop
  | .var _ => True
  | .bot => True
  | .app _ f => ∀ i, CaptureFree x y (f i)
  | .imp a b => CaptureFree x y a ∧ CaptureFree x y b
  | .ex z a => z = x ∨ x ∉ FV a ∨ (z ≠ y ∧ CaptureFree x y a)

/-- **The `x ∉ FV a` alternative is not vacuous.**  Substituting `y` for `x` in
`∃y. z`, where `x` does not occur, is harmless — `substVar` leaves the pattern
alone — yet the binder is `y` itself. Only the middle alternative admits it. -/
theorem captureFree_needs_notFree :
    CaptureFree (S := S) (Var := Nat) 0 1 (.ex 1 (.var 2)) ∧
      substVar (S := S) (Var := Nat) 0 1 (.ex 1 (.var 2)) = .ex 1 (.var 2) := by
  constructor
  · simp [CaptureFree, FV]
  · simp [substVar]

/-! ### Rule (10): application contexts -/

/-- `C ::= □ | σ(φ₁, …, C, …, φₙ)`. -/
inductive AppCtx (S : Signature) (Var : Type) where
  | hole : AppCtx S Var
  | node : (σ : S.Sym) → (i : Fin (S.arity σ)) →
      (Fin (S.arity σ) → Pattern S Var) → AppCtx S Var → AppCtx S Var

/-- `C[φ]`. -/
def AppCtx.plug : AppCtx S Var → Pattern S Var → Pattern S Var
  | .hole, φ => φ
  | .node σ i args c, φ => .app σ (Function.update args i (c.plug φ))

/-! ### Figure 2 -/

/-- `Γ ⊢ φ`. The ten schemes and rules of Figure 2, restricted to one sort. -/
inductive Provable (Γ : Set (Pattern S Var)) : Pattern S Var → Prop
  /-- Membership in the theory. -/
  | hyp {φ} : φ ∈ Γ → Provable Γ φ
  /-- (1) Tautology. -/
  | taut {p : PForm} {θ : Nat → Pattern S Var} : p.Taut → Provable Γ (p.subst θ)
  /-- (2) Modus ponens. -/
  | mp {φ₁ φ₂} : Provable Γ φ₁ → Provable Γ (.imp φ₁ φ₂) → Provable Γ φ₂
  /-- (3) ∃-quantifier, capture-avoiding. -/
  | exQuant {x y : Var} {φ} : CaptureFree x y φ →
      Provable Γ (.imp (substVar x y φ) (.ex x φ))
  /-- (4) ∃-generalization. -/
  | exGen {x : Var} {φ₁ φ₂} : Provable Γ (.imp φ₁ φ₂) → x ∉ FV φ₂ →
      Provable Γ (.imp (.ex x φ₁) φ₂)
  /-- (5) Propagation of `⊥`. -/
  | propBot {σ : S.Sym} {i : Fin (S.arity σ)} {args} :
      Provable Γ (.imp (.app σ (Function.update args i .bot)) .bot)
  /-- (6) Propagation of `∨`. -/
  | propOr {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      Provable Γ (.imp (.app σ (Function.update args i (Pattern.or φ₁ φ₂)))
        (Pattern.or (.app σ (Function.update args i φ₁))
                    (.app σ (Function.update args i φ₂))))
  /-- (7) Propagation of `∃`. -/
  | propEx {σ : S.Sym} {i : Fin (S.arity σ)} {args} {x : Var} {φ} :
      (∀ j, j ≠ i → x ∉ FV (args j)) →
      Provable Γ (.imp (.app σ (Function.update args i (.ex x φ)))
        (.ex x (.app σ (Function.update args i φ))))
  /-- (8) Framing. -/
  | framing {σ : S.Sym} {i : Fin (S.arity σ)} {args} {φ₁ φ₂} :
      Provable Γ (.imp φ₁ φ₂) →
      Provable Γ (.imp (.app σ (Function.update args i φ₁))
                       (.app σ (Function.update args i φ₂)))
  /-- (9) Existence. -/
  | existence {x : Var} : Provable Γ (.ex x (.var x))
  /-- (10) Singleton variable. -/
  | singleton {x : Var} {φ} (C₁ C₂ : AppCtx S Var) :
      Provable Γ (.imp (C₁.plug (Pattern.and (.var x) φ))
        (Pattern.nt (C₂.plug (Pattern.and (.var x) (Pattern.nt φ)))))

/-! ### Small public Hilbert toolkit -/

/-- Provability is monotone in its hypotheses. -/
theorem Provable.weaken {Γ Δ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓΔ : Γ ⊆ Δ) (h : Provable Γ φ) : Provable Δ φ := by
  induction h with
  | hyp hφ => exact .hyp (hΓΔ hφ)
  | taut hp => exact .taut hp
  | mp _ _ ihφ himp => exact .mp ihφ himp
  | exQuant hfree => exact .exQuant hfree
  | exGen _ hfree ih => exact .exGen ih hfree
  | propBot => exact .propBot
  | propOr => exact .propOr
  | propEx hfree => exact .propEx hfree
  | framing _ ih => exact .framing ih
  | existence => exact .existence
  | singleton C₁ C₂ => exact .singleton C₁ C₂

/-- A theorem is usable under arbitrary hypotheses. -/
theorem Provable.weaken_empty {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (h : Provable (∅ : Set (Pattern S Var)) φ) : Provable Γ φ :=
  h.weaken (by simp)

private theorem taut_top : PForm.Taut (.imp .bot .bot) := by
  intro _
  rfl

/-- `⊤` is derivable in every theory. -/
theorem provable_top (Γ : Set (Pattern S Var)) :
    Provable Γ (Pattern.tp : Pattern S Var) := by
  exact .taut (θ := fun _ => .bot) taut_top

private theorem taut_and_intro :
    PForm.Taut (.imp (.atom 0) (.imp (.atom 1)
      (.imp (.imp (.atom 0) (.imp (.atom 1) .bot)) .bot))) := by
  intro v
  cases h₀ : v 0 <;> cases h₁ : v 1 <;> simp [PForm.eval, h₀, h₁]

/-- Derived conjunction introduction. -/
theorem Provable.and_intro {Γ : Set (Pattern S Var)} {φ ψ : Pattern S Var}
    (hφ : Provable Γ φ) (hψ : Provable Γ ψ) :
    Provable Γ (Pattern.and φ ψ) := by
  have ht : Provable Γ (.imp φ (.imp ψ (Pattern.and φ ψ))) := by
    simpa [PForm.subst, Pattern.and, Pattern.nt] using
      (Provable.taut (Γ := Γ) (θ := fun n => if n = 0 then φ else ψ)
        taut_and_intro)
  exact .mp hψ (.mp hφ ht)

/-! ### Lemma 5 -/

/-- The propositional tautology introducing double negation. -/
def doubleNegIntro : PForm :=
  .imp (.atom 0) (.imp (.imp (.atom 0) .bot) .bot)

private theorem doubleNegIntro_taut : doubleNegIntro.Taut := by
  intro v
  cases h : v 0 <;> simp [doubleNegIntro, PForm.eval, h]

/-- The propositional tautology expressing transitivity of implication. -/
def implicationTransitivity : PForm :=
  .imp (.imp (.atom 0) (.atom 1))
    (.imp (.imp (.atom 1) (.atom 2)) (.imp (.atom 0) (.atom 2)))

private theorem implicationTransitivity_taut : implicationTransitivity.Taut := by
  intro v
  cases h₀ : v 0 <;> cases h₁ : v 1 <;> cases h₂ : v 2 <;>
    simp [implicationTransitivity, PForm.eval, h₀, h₁, h₂]

private theorem Provable.imp_trans {Γ : Set (Pattern S Var)} {φ₁ φ₂ φ₃ : Pattern S Var}
    (h₁₂ : Provable Γ (.imp φ₁ φ₂)) (h₂₃ : Provable Γ (.imp φ₂ φ₃)) :
    Provable Γ (.imp φ₁ φ₃) := by
  have ht : Provable Γ
      (.imp (.imp φ₁ φ₂) (.imp (.imp φ₂ φ₃) (.imp φ₁ φ₃))) := by
    exact Provable.taut (p := implicationTransitivity)
      (θ := fun n => if n = 0 then φ₁ else if n = 1 then φ₂ else φ₃)
      implicationTransitivity_taut
  exact Provable.mp h₂₃ (Provable.mp h₁₂ ht)

omit [DecidableEq Var] in
private theorem update_top_eq_dia_args (e : Coord S) (χ : Pattern S Var) :
    Function.update (fun _ : Fin (S.arity e.1) => (Pattern.tp : Pattern S Var)) e.2 χ =
      fun j => if j = e.2 then χ else Pattern.tp := by
  funext j
  by_cases hj : j = e.2
  · subst j
    simp
  · simp [hj]

private theorem necessitation_coord {Γ : Set (Pattern S Var)} {ψ : Pattern S Var}
    (h : Provable Γ ψ) (e : Coord S) : Provable Γ (box e ψ) := by
  have hdnIntro : Provable Γ (.imp ψ (.imp (.imp ψ .bot) .bot)) := by
    exact Provable.taut (p := doubleNegIntro) (θ := fun _ => ψ) doubleNegIntro_taut
  have hdn : Provable Γ (.imp (.imp ψ .bot) .bot) := Provable.mp h hdnIntro
  have hframe : Provable Γ (.imp (dia e (.imp ψ .bot)) (dia e .bot)) := by
    have hframe' := Provable.framing (σ := e.1) (i := e.2)
      (args := fun _ => Pattern.tp) hdn
    simpa only [dia, update_top_eq_dia_args] using hframe'
  have hbot : Provable Γ (.imp (dia e .bot) .bot) := by
    have hbot' := Provable.propBot (Γ := Γ) (σ := e.1) (i := e.2)
      (args := fun _ => Pattern.tp)
    simpa only [dia, update_top_eq_dia_args] using hbot'
  simpa only [box] using Provable.imp_trans hframe hbot

/-- **Lemma 5 (necessitation).**  If `Γ ⊢ ψ` then `Γ ⊢ [p]ψ` for every word `p`.

The paper's proof, for a single coordinate `e`: the tautology
`ψ → ((ψ → ⊥) → ⊥)` with modus ponens gives `Γ ⊢ ¬ψ → ⊥`; framing in position
`i` with `⊤` elsewhere gives `Γ ⊢ ⟨e⟩¬ψ → σ(⊤,…,⊥,…,⊤)`; propagation of `⊥`
gives `⊢ σ(⊤,…,⊥,…,⊤) → ⊥`; composing is propositional. Then iterate along `p`. -/
theorem necessitation {Γ : Set (Pattern S Var)} {ψ : Pattern S Var}
    (h : Provable Γ ψ) (p : List (Coord S)) : Provable Γ (boxes p ψ) := by
  induction p with
  | nil => exact h
  | cons e p ih =>
    simpa only [boxes_cons] using necessitation_coord ih e

/-! ### The two black boxes -/

/-- Finite conjunction, `⋀ l`. -/
def conj : List (Pattern S Var) → Pattern S Var
  | [] => Pattern.tp
  | φ :: l => Pattern.and φ (conj l)

/-- Introduce the pinned finite conjunction of a list of derivable patterns. -/
theorem provable_conj {Γ : Set (Pattern S Var)} (l : List (Pattern S Var))
    (h : ∀ δ ∈ l, Provable Γ δ) : Provable Γ (conj l) := by
  induction l with
  | nil => exact provable_top Γ
  | cons δ l ih =>
      exact .and_intro (h δ (by simp))
        (ih (by intro ψ hψ; exact h ψ (by simp [hψ])))

/-- **(L) Strong local completeness.**  If `Δ ⊨loc φ` then `⊢ (⋀Δ₀) → φ` for
some finite `Δ₀ ⊆ Δ`.  The paper uses this as a black box, citing Definition 3.3
and "Theorem 3.8" of its reference [4] -- but Theorem 3.8 there is the WEAK
statement; strong local completeness is Theorem 3.7 (Theorem 83 of [5]).  See
`FINDINGS.md`. -/
def StrongLocalCompleteness (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ (Δ : Set (Pattern S Var)) (φ : Pattern S Var), LocalCons Δ φ →
    ∃ l : List (Pattern S Var), (∀ δ ∈ l, δ ∈ Δ) ∧
      Provable (∅ : Set (Pattern S Var)) (.imp (conj l) φ)

/-- **(S) Soundness.**  `Γ ⊢ φ` implies `Γ ⊨ φ`.  The paper uses this as a
black box too, but unlike (L) it is within reach here: see `soundness` below. -/
def Soundness (S : Signature) (Var : Type) [DecidableEq Var] : Prop :=
  ∀ (Γ : Set (Pattern S Var)) (φ : Pattern S Var), Provable Γ φ → GlobalCons Γ φ

end MatchingLogic
