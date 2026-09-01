/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Coordinates, boxes, and word-indexed reachability
(arXiv:2608.13306v1, Section 3, Definitions 2-3 and Lemma 4).

Definitions are written by the coordinating session from the paper; the statements below were pinned
before any proof was attempted.
-/
import LeanPool.MatchingLogic.Semantics

/-!
# MatchingLogic.Boxes
-/

namespace MatchingLogic

variable {S : Signature} {Var : Type}

/-- A coordinate is a pair `(σ, i)` with `σ` of arity `n ≥ 1` and `1 ≤ i ≤ n`
(Definition 2).  Constants have no coordinates: `Fin 0` is empty, so no
coordinate has a constant as its first component. -/
abbrev Coord (S : Signature) : Type := (σ : S.Sym) × Fin (S.arity σ)

/-- `⟨e⟩ψ := σ(⊤, …, ψ, …, ⊤)` with `ψ` in position `i` (Definition 3). -/
def dia (e : Coord S) (ψ : Pattern S Var) : Pattern S Var :=
  .app e.1 (fun j => if j = e.2 then ψ else Pattern.tp)

/-- `[e]ψ := ⟨e⟩(ψ → ⊥) → ⊥` (Definition 3). -/
def box (e : Coord S) (ψ : Pattern S Var) : Pattern S Var :=
  .imp (dia e (.imp ψ .bot)) .bot

/-- `[p]ψ := [e₁]⋯[eₘ]ψ` for a word `p = e₁⋯eₘ`, with `[ε]ψ := ψ`
(Definition 3).  Words are lists of coordinates; every word composes because
there is only one sort. -/
def boxes : List (Coord S) → Pattern S Var → Pattern S Var
  | [], ψ => ψ
  | e :: p, ψ => box e (boxes p ψ)

@[simp] theorem boxes_nil (ψ : Pattern S Var) : boxes [] ψ = ψ := rfl
@[simp] theorem boxes_cons (e : Coord S) (p : List (Coord S)) (ψ : Pattern S Var) :
    boxes (e :: p) ψ = box e (boxes p ψ) := rfl

namespace Model

/-- One backward step along a single coordinate: `u ⇝_e v` (Definition 2). -/
def stepAt (M : Model S) (e : Coord S) (u v : M.carrier) : Prop :=
  ∃ a : Fin (S.arity e.1) → M.carrier, u ∈ M.interp e.1 a ∧ v = a e.2

/-- `⇝_p` for a word `p`, the relational composite, with `⇝_ε = id`
(Definition 2). -/
def reachWord (M : Model S) : List (Coord S) → M.carrier → M.carrier → Prop
  | [], u, v => u = v
  | e :: p, u, v => ∃ w, M.stepAt e u w ∧ M.reachWord p w v

variable (M : Model S)

@[simp] theorem reachWord_nil (u v : M.carrier) : M.reachWord [] u v ↔ u = v := Iff.rfl

@[simp] theorem reachWord_cons (e : Coord S) (p : List (Coord S)) (u v : M.carrier) :
    M.reachWord (e :: p) u v ↔ ∃ w, M.stepAt e u w ∧ M.reachWord p w v := Iff.rfl

/-- `⇝` of Definition 2 is the union of the `⇝_e` over all coordinates. -/
theorem step_iff_exists_coord (u v : M.carrier) :
    M.Step u v ↔ ∃ e : Coord S, M.stepAt e u v := by
  constructor
  · rintro ⟨σ, a, i, ha, hv⟩
    exact ⟨⟨σ, i⟩, a, ha, hv⟩
  · rintro ⟨⟨σ, i⟩, a, ha, hv⟩
    exact ⟨σ, a, i, ha, hv⟩

/-- `⇝*` is reachability along some word. -/
theorem reflTransGen_step_iff_exists_word (u v : M.carrier) :
    Relation.ReflTransGen M.Step u v ↔ ∃ p : List (Coord S), M.reachWord p u v := by
  constructor
  · intro h
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl⟩
    | head hac _ ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨e, he⟩ := (M.step_iff_exists_coord _ _).mp hac
      exact ⟨e :: p, _, he, hp⟩
  · rintro ⟨p, hp⟩
    induction p generalizing u with
    | nil =>
      simp only [Model.reachWord_nil] at hp
      exact hp ▸ Relation.ReflTransGen.refl
    | cons e p ih =>
      obtain ⟨w, hstep, hrest⟩ := (M.reachWord_cons e p u v).mp hp
      exact Relation.ReflTransGen.head ((M.step_iff_exists_coord u w).mpr ⟨e, hstep⟩) (ih w hrest)

end Model

section Denotation

variable [DecidableEq Var]

/-- The denotation of `⟨e⟩ψ`: the points with an `e`-successor in `ψ`. -/
theorem denote_dia (M : Model S) (ρ : Var → M.carrier) (e : Coord S)
    (ψ : Pattern S Var) :
    M.denote ρ (dia e ψ) = {u | ∃ v, M.stepAt e u v ∧ v ∈ M.denote ρ ψ} := by
  ext u
  simp only [dia, denote_app, Model.app, Model.stepAt, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a e.2, ⟨a, hu, rfl⟩, by simpa using ha e.2⟩
  · rintro ⟨v, ⟨a, hu, rfl⟩, hv⟩
    refine ⟨a, fun j => ?_, hu⟩
    by_cases hj : j = e.2
    · subst hj; simpa using hv
    · simp [hj]

/-- Auxiliary: the denotation of `[e]ψ` is the points all of whose `e`-successors
lie in `⟦ψ⟧`.  This is the complement step of the paper's proof of Lemma 4,
factored out so the word induction below only has to compose it with itself. -/
theorem denote_box (M : Model S) (ρ : Var → M.carrier) (e : Coord S)
    (ψ : Pattern S Var) :
    M.denote ρ (box e ψ) = {u | ∀ v, M.stepAt e u v → v ∈ M.denote ρ ψ} := by
  ext u
  simp only [box, denote_imp, denote_bot, Set.union_empty, denote_dia, Set.mem_compl_iff,
    Set.mem_ofPred_eq]
  constructor
  · intro h v hstep
    by_contra hv
    exact h ⟨v, hstep, hv⟩
  · rintro h ⟨v, hstep, hv⟩
    exact hv (h v hstep)

/-- **Lemma 4 (box semantics).**  `⟦[p]ψ⟧ = {u | ⇝_p[u] ⊆ ⟦ψ⟧}`.

The paper states this for closed `ψ`, because it writes both sides with `⟦·⟧`.
No closedness hypothesis is needed here, and the reason is `FV_boxes` below:
`dia`, `box` and `boxes` are binder-free, so `FV ([p]ψ) = FV ψ` exactly and both
sides read ψ's free variables off the same `ρ`.  (Merely "both sides carry the
same valuation" would NOT suffice -- a box that introduced a binder would
evaluate ψ under an updated valuation on the left and not on the right.)
Instantiating at a closed `ψ` recovers the paper's statement. -/
theorem denote_boxes (M : Model S) (ρ : Var → M.carrier) (p : List (Coord S))
    (ψ : Pattern S Var) :
    M.denote ρ (boxes p ψ) = {u | ∀ v, M.reachWord p u v → v ∈ M.denote ρ ψ} := by
  induction p with
  | nil =>
    ext u
    simp
  | cons e p ih =>
    ext u
    simp only [boxes_cons, denote_box, Model.reachWord_cons, Set.mem_ofPred_eq]
    constructor
    · rintro h v ⟨w, hstep, hrest⟩
      have hw : w ∈ M.denote ρ (boxes p ψ) := h w hstep
      rw [ih] at hw
      exact hw v hrest
    · intro h v hstep
      rw [ih]
      intro w hrest
      exact h w ⟨v, hstep, hrest⟩

end Denotation

/-! ### Boxing is binder-free, and concatenation decomposes the same way on
both sides.

`FV_boxes` is what licenses dropping the closedness hypothesis from Lemma 4,
and is also what `Localization.closed_of_mem_localize` needs.  The two `append`
lemmas are the real order check: `boxes` and `reachWord` must decompose a
concatenated word identically, or a jointly flipped pair would go unnoticed. -/

@[simp] theorem FV_dia (e : Coord S) (ψ : Pattern S Var) : FV (dia e ψ) = FV ψ := by
  apply Set.Subset.antisymm
  · simp only [dia, FV_app]
    apply Set.iUnion_subset
    intro i
    split_ifs with h
    · exact le_refl _
    · simp [Pattern.tp]
  · simp only [dia, FV_app]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨e.2, by simpa using hx⟩

@[simp] theorem FV_box (e : Coord S) (ψ : Pattern S Var) : FV (box e ψ) = FV ψ := by
  simp [box]

@[simp] theorem FV_boxes (p : List (Coord S)) (ψ : Pattern S Var) :
    FV (boxes p ψ) = FV ψ := by
  induction p with
  | nil => simp
  | cons e p ih => simp [ih]

theorem closed_boxes (p : List (Coord S)) (ψ : Pattern S Var) :
    Closed (boxes p ψ) ↔ Closed ψ := by
  unfold Closed
  rw [FV_boxes]

theorem boxes_append (p q : List (Coord S)) (ψ : Pattern S Var) :
    boxes (p ++ q) ψ = boxes p (boxes q ψ) := by
  induction p with
  | nil => simp
  | cons e p ih => simp [ih]

theorem Model.reachWord_append (M : Model S) (p q : List (Coord S)) (u v : M.carrier) :
    M.reachWord (p ++ q) u v ↔ ∃ w, M.reachWord p u w ∧ M.reachWord q w v := by
  induction p generalizing u with
  | nil => simp
  | cons e p ih =>
    simp only [List.cons_append, Model.reachWord_cons]
    constructor
    · rintro ⟨w, hstep, hrest⟩
      obtain ⟨w', hp, hq⟩ := (ih (u := w)).mp hrest
      exact ⟨w', ⟨w, hstep, hp⟩, hq⟩
    · rintro ⟨w', ⟨w, hstep, hp⟩, hq⟩
      exact ⟨w, hstep, (ih (u := w)).mpr ⟨w', hp, hq⟩⟩

end MatchingLogic
