/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Corollary 16 — conservativity of definedness. arXiv:2608.13306v1, Section 5.

  "**Corollary 16 (conservativity of definedness).** If Γ and φ are
   definedness-free, then Γ ∪ {⌈x⌉} ⊢ φ implies Γ ⊢ φ.

   *Proof.* Soundness in the enriched signature gives Γ ∪ {⌈x⌉} ⊨ φ (Figure 2 is
   sound for every signature). Every definedness-free M ⊨ Γ expands to a model of
   Γ ∪ {⌈x⌉}, so M ⊨ φ. Hence Γ ⊨ φ, and Corollary 15 applies."

Adding definedness to the language cannot prove new definedness-free theorems.
This is the first result here that DEPENDS on Corollary 15, so it only became
reachable once the proof-theoretic half landed.

DESIGN RULINGS:

* The enriched signature is `defSig S`, whose symbols are `Option S.Sym` with
  `none` the unary definedness symbol. `emb` embeds definedness-free patterns
  into it. Nothing in `Core.lean` changes; the base development stays
  definedness-free, as the paper's whole subject requires.
* Definedness is not a new semantic clause. It is an ordinary symbol whose
  interpretation is forced by the axiom `⌈x⌉`: interpreting it as constantly
  `univ` on singletons makes the pointwise extension give `univ` on nonempty
  arguments and `∅` on empty ones, which is exactly `ρ(⌈φ⌉)` of Section 2.
* (L) stays a hypothesis, inherited from Corollary 15. (S) does not: `soundness`
  is a theorem, and it holds at every signature, `defSig S` included.

Statements pinned before any proof was attempted.
-/
import LeanPool.MatchingLogic.EntryPoints

/-!
# MatchingLogic.Definedness
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type} [DecidableEq Var]

/-- The signature enriched with a unary definedness symbol, written `none`. -/
abbrev defSig (S : Signature) : Signature :=
  ⟨Option S.Sym, fun s => match s with | none => 1 | some σ => S.arity σ⟩

/-- Definedness-free patterns embed into the enriched language. -/
def emb : Pattern S Var → Pattern (defSig S) Var
  | .var x => .var x
  | .bot => .bot
  | .imp a b => .imp (emb a) (emb b)
  | .ex x a => .ex x (emb a)
  | .app σ f => .app (some σ) (fun i => emb (f i))

/-- `⌈φ⌉`. -/
def defined (φ : Pattern (defSig S) Var) : Pattern (defSig S) Var :=
  .app none (fun _ => φ)

/-- The axiom `⌈x⌉` of the paper. -/
def definednessAxiom (x : Var) : Pattern (defSig S) Var := defined (.var x)

/-- The expansion of a definedness-free model: the same carrier, the same
symbols, and definedness interpreted as constantly everything on singletons —
which the pointwise extension turns into `univ` on nonempty arguments and `∅`
on empty ones. -/
def expand (M : Model S) : Model (defSig S) where
  carrier := M.carrier
  nonempty := M.nonempty
  interp := fun s => match s with
    | none => fun _ => Set.univ
    | some σ => fun a => M.interp σ a

/-- The embedding preserves denotation. -/
theorem denote_emb (M : Model S) (ρ : Var → M.carrier) (φ : Pattern S Var) :
    (expand M).denote ρ (emb φ) = M.denote ρ φ := by
  unfold expand
  induction φ generalizing ρ with
  | var x => rfl
  | bot => rfl
  | app σ f ih =>
      simp only [emb, denote_app]
      ext u
      constructor
      · rintro ⟨a, ha, hu⟩
        refine ⟨a, ?_, hu⟩
        intro i
        have hi := Set.ext_iff.mp (ih i ρ) (a i)
        exact hi.mp (by simpa only using ha i)
      · rintro ⟨a, ha, hu⟩
        refine ⟨a, ?_, hu⟩
        intro i
        have hi := Set.ext_iff.mp (ih i ρ) (a i)
        exact hi.mpr (by simpa only using ha i)
  | imp φ ψ ihφ ihψ =>
      simp only [emb, denote_imp]
      rw [ihφ, ihψ]
  | ex x φ ih =>
      simp only [emb, denote_ex]
      ext u
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, (ih (Function.update ρ x a)) ▸ ha⟩
      · rintro ⟨a, ha⟩
        exact ⟨a, (ih (Function.update ρ x a)).symm ▸ ha⟩

/-- The expansion satisfies the definedness axiom, so it really is a model of
`Γ ∪ {⌈x⌉}` whenever `M` is a model of `Γ`. -/
theorem expand_sat_definednessAxiom (M : Model S) (x : Var) :
    (expand M).Sat (definednessAxiom (S := S) x) := by
  intro ρ
  unfold Model.Total
  change (expand M).app none (fun _ => ({ρ x} : Set M.carrier)) = Set.univ
  apply Set.eq_univ_iff_forall.mpr
  intro u
  exact ⟨fun _ => ρ x, fun _ => Set.mem_singleton (ρ x), Set.mem_univ u⟩

/-- `⌈·⌉` has the semantics of Section 2 in the expansion: `univ` when the
argument is inhabited, `∅` when it is empty.  This is a control: if it failed,
`expand` would not be interpreting definedness. -/
theorem denote_defined (M : Model S) (ρ : Var → M.carrier)
    (φ : Pattern (defSig S) Var) :
    ((expand M).denote ρ (defined φ) = Set.univ ↔ ((expand M).denote ρ φ).Nonempty) ∧
      ((expand M).denote ρ (defined φ) = ∅ ↔ (expand M).denote ρ φ = ∅) := by
  have hmem (u : M.carrier) :
      u ∈ (expand M).denote ρ (defined φ) ↔
        ((expand M).denote ρ φ).Nonempty := by
    constructor
    · rintro ⟨a, ha, -⟩
      exact ⟨a 0, ha 0⟩
    · rintro ⟨a, ha⟩
      exact ⟨fun _ => a, fun _ => ha, Set.mem_univ u⟩
  constructor
  · constructor
    · intro h
      let u : M.carrier := Classical.choice M.nonempty
      apply (hmem u).mp
      rw [h]
      exact Set.mem_univ u
    · intro ha
      apply Set.eq_univ_iff_forall.mpr
      intro u
      exact (hmem u).mpr ha
  · constructor
    · intro h
      ext a
      simp only [Set.mem_empty_iff_false, iff_false]
      intro ha
      have hu := (hmem a).mpr ⟨a, ha⟩
      rw [h] at hu
      exact hu
    · intro h
      ext u
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hu
      obtain ⟨a, ha⟩ := (hmem u).mp hu
      rw [h] at ha
      exact ha

/-- **Corollary 16 (conservativity of definedness).**

Note (S) is supplied rather than assumed — `soundness` is a theorem here, and it
holds at `defSig S` as at any signature.  (L) remains a hypothesis, inherited
from Corollary 15, and is needed at the BASE signature only. -/
theorem definedness_conservative
    (hL : StrongLocalCompleteness S Var)
    {Γ : Set (Pattern S Var)} {φ : Pattern S Var}
    (hΓ : ∀ γ ∈ Γ, Closed γ) (hφ : Closed φ) (x : Var)
    (h : Provable (emb '' Γ ∪ {definednessAxiom (S := S) x}) (emb φ)) :
    Provable Γ φ := by
  apply (global_completeness_of_localCompleteness hL hΓ hφ).mp
  intro M hM
  have henriched : GlobalCons (emb '' Γ ∪ {definednessAxiom (S := S) x}) (emb φ) :=
    soundness _ _ h
  have htheory : (expand M).SatSet
      (emb '' Γ ∪ {definednessAxiom (S := S) x}) := by
    intro ψ hψ
    rcases hψ with hψ | hψ
    · obtain ⟨γ, hγ, rfl⟩ := hψ
      intro ρ
      change Var → M.carrier at ρ
      exact (denote_emb M ρ γ).trans (hM γ hγ ρ)
    · rw [Set.mem_singleton_iff] at hψ
      subst ψ
      exact expand_sat_definednessAxiom M x
  have hemb := henriched (expand M) htheory
  intro ρ
  exact (denote_emb M ρ φ).symm.trans (hemb ρ)

end MatchingLogic
