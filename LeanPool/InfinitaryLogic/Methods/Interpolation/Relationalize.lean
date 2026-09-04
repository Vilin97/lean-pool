/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.TermGraph
/-!
# Relationalization of formulas (Craig Layer 3, Unit 4)

The formula translation into the relationalized language: `relationalizeFormula` sends an
`L_{ω₁ω}` formula over `L` to one over `graphLanguage L`, replacing every atom by its
term-graph flattening and transporting the connectives and quantifiers structurally.

## Atomic translation

* `equalGraph t u` — **one** witness, not two: `∃ y, termGraph(t, y) ∧ termGraph(u, y)`.
  Smaller than two witnesses plus an equality atom, and its relation-symbol set is exactly the
  graph symbols occurring in `t` or `u`.
* `relGraph R ts` — `∃ y⃗, (⋀ᵢ termGraph(tᵢ, yᵢ)) ∧ R^base(y⃗)`.

Both consume `existsBlock` directly, with the context-polymorphic `termGraphAux` fed by the
lifted variable embedding `ctxLiftEmb` (no term relabeling of built formulas).

## Main Results

* `realize_equalGraph` / `realize_relGraph` — the atomic realization lemmas, kept separate so a
  failure downstream distinguishes term-flattening trouble from connective transport.
* `realize_relationalizeFormula` — over the graph expansion, the translation is
  realization-equivalent to the original formula.
* `relationsIn_relationalizeFormula` — the **exact** occurrence identity
  `(relationalizeFormula φ).relationsIn = relSym L φ.functionsIn φ.relationsIn`; it composes
  immediately with `relSym_inter`, making the final sharp occurrence bound essentially
  algebraic. `functionsIn_relationalizeFormula` is `∅` (the graph language is relational).
* The nested-formula pilot `R(f(g(x), h(c)))`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {α : Type} {n : ℕ}

/-! ## The lifted variable embedding and the atomic translations -/

/-- The variable embedding of the ambient context into the context extended by `k` fresh bound
variables — what `termGraphAux` reads the atom's term variables through. -/
def ctxLiftEmb (k : ℕ) (z : α ⊕ Fin n) : (graphLanguage L).Term (α ⊕ Fin (n + k)) :=
  Term.var (Sum.map id (Fin.castAdd k) z)

/-- The equality atom, relationalized with **one** witness: `∃ y, termGraph(t,y) ∧
termGraph(u,y)`. -/
def equalGraph (t u : L.Term (α ⊕ Fin n)) : (graphLanguage L).BoundedFormulaω α n :=
  .existsBlock (k := 1)
    ((termGraphAux t (ctxLiftEmb 1) (graphWitnessVar n 0)).and
      (termGraphAux u (ctxLiftEmb 1) (graphWitnessVar n 0)))

/-- The relation atom, relationalized: `∃ y⃗, (⋀ᵢ termGraph(tᵢ, yᵢ)) ∧ R^base(y⃗)`. -/
def relGraph {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) :
    (graphLanguage L).BoundedFormulaω α n :=
  .existsBlock
    ((BoundedFormulaω.einf fun i => termGraphAux (ts i) (ctxLiftEmb k) (graphWitnessVar n i)).and
      (.rel (GraphRelation.base R) fun i => graphWitnessVar n i))

/-! ## The structural translation -/

/-- Relationalize a formula: atoms via their term-graph flattenings (`equalGraph`/`relGraph`),
connectives and quantifiers structurally. -/
def relationalizeFormula : ∀ {n : ℕ}, L.BoundedFormulaω α n →
    (graphLanguage L).BoundedFormulaω α n
  | _, .falsum => .falsum
  | _, .equal t u => equalGraph t u
  | _, .rel R ts => relGraph R ts
  | _, .imp φ ψ => (relationalizeFormula φ).imp (relationalizeFormula ψ)
  | _, .all φ => (relationalizeFormula φ).all
  | _, .iSup φs => .iSup fun i => relationalizeFormula (φs i)
  | _, .iInf φs => .iInf fun i => relationalizeFormula (φs i)

/-! Stable rewrite points for Units 5–7 (all definitional). -/

@[simp] theorem relationalizeFormula_falsum :
    relationalizeFormula (.falsum : L.BoundedFormulaω α n) = .falsum := rfl

@[simp] theorem relationalizeFormula_equal (t u : L.Term (α ⊕ Fin n)) :
    relationalizeFormula (.equal t u) = equalGraph t u := rfl

@[simp] theorem relationalizeFormula_rel {k : ℕ} (R : L.Relations k)
    (ts : Fin k → L.Term (α ⊕ Fin n)) :
    relationalizeFormula (.rel R ts) = relGraph R ts := rfl

@[simp] theorem relationalizeFormula_imp (φ ψ : L.BoundedFormulaω α n) :
    relationalizeFormula (φ.imp ψ) =
      (relationalizeFormula φ).imp (relationalizeFormula ψ) := rfl

@[simp] theorem relationalizeFormula_all (φ : L.BoundedFormulaω α (n + 1)) :
    relationalizeFormula φ.all = (relationalizeFormula φ).all := rfl

@[simp] theorem relationalizeFormula_iSup (φs : ℕ → L.BoundedFormulaω α n) :
    relationalizeFormula (.iSup φs) = .iSup fun i => relationalizeFormula (φs i) := rfl

@[simp] theorem relationalizeFormula_iInf (φs : ℕ → L.BoundedFormulaω α n) :
    relationalizeFormula (.iInf φs) = .iInf fun i => relationalizeFormula (φs i) := rfl

/-! ## Semantics over the graph expansion -/

section Semantics

attribute [local instance] graphExpansion

variable {M : Type} [L.Structure M]

@[simp] theorem realize_ctxLiftEmb {k : ℕ} (z : α ⊕ Fin n)
    (v : α → M) (xs : Fin n → M) (ws : Fin k → M) :
    (ctxLiftEmb (L := L) k z).realize (Sum.elim v (Fin.append xs ws)) = Sum.elim v xs z := by
  rcases z with a | i
  · rfl
  · exact Fin.append_left xs ws i

/-- The single-witness value lemma shared by both atomic realization proofs. -/
private theorem realize_termGraphAux_ctxLift {k : ℕ} (w : L.Term (α ⊕ Fin n)) (i : Fin k)
    (v : α → M) (xs : Fin n → M) (ws : Fin k → M) :
    (termGraphAux w (ctxLiftEmb k) (graphWitnessVar n i)).Realize v (Fin.append xs ws) ↔
      w.realize (Sum.elim v xs) = ws i := by
  rw [realize_termGraphAux]
  simp only [realize_ctxLiftEmb, realize_graphWitnessVar]

/-- **Atomic realization, equality**: the one-witness translation of `t = u` realizes to value
equality. -/
theorem realize_equalGraph (t u : L.Term (α ⊕ Fin n)) (v : α → M) (xs : Fin n → M) :
    (equalGraph t u).Realize v xs ↔
      t.realize (Sum.elim v xs) = u.realize (Sum.elim v xs) := by
  rw [equalGraph, BoundedFormulaω.realize_existsBlock]
  constructor
  · rintro ⟨ws, hw⟩
    rw [BoundedFormulaω.realize_and, realize_termGraphAux_ctxLift,
      realize_termGraphAux_ctxLift] at hw
    exact hw.1.trans hw.2.symm
  · intro h
    refine ⟨fun _ => u.realize (Sum.elim v xs), ?_⟩
    rw [BoundedFormulaω.realize_and, realize_termGraphAux_ctxLift, realize_termGraphAux_ctxLift]
    exact ⟨h, rfl⟩

/-- **Atomic realization, relations**: the translation of `R(t₀, …, t_{k-1})` realizes to the
base relation on the terms' values. -/
theorem realize_relGraph {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n))
    (v : α → M) (xs : Fin n → M) :
    (relGraph R ts).Realize v xs ↔
      RelMap R fun i => (ts i).realize (Sum.elim v xs) := by
  rw [relGraph, BoundedFormulaω.realize_existsBlock]
  constructor
  · rintro ⟨ws, hw⟩
    rw [BoundedFormulaω.realize_and, BoundedFormulaω.realize_einf] at hw
    obtain ⟨hconj, hatom⟩ := hw
    rw [BoundedFormulaω.realize_rel, graphExpansion_relMap_base] at hatom
    simp only [realize_graphWitnessVar] at hatom
    rw [show (fun i => (ts i).realize (Sum.elim v xs)) = ws from
      funext fun i => (realize_termGraphAux_ctxLift (ts i) i v xs ws).mp (hconj i)]
    exact hatom
  · intro h
    refine ⟨fun i => (ts i).realize (Sum.elim v xs), ?_⟩
    rw [BoundedFormulaω.realize_and, BoundedFormulaω.realize_einf]
    refine ⟨fun i => (realize_termGraphAux_ctxLift _ i v xs _).mpr rfl, ?_⟩
    rw [BoundedFormulaω.realize_rel, graphExpansion_relMap_base]
    simpa only [realize_graphWitnessVar] using h

/-- **The realize bridge**: over the graph expansion, the relationalized formula is
realization-equivalent to the original. -/
theorem realize_relationalizeFormula :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (v : α → M) (xs : Fin n → M),
      (relationalizeFormula φ).Realize v xs ↔ φ.Realize v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t u, v, xs => realize_equalGraph t u v xs
  | _, .rel R ts, v, xs => realize_relGraph R ts v xs
  | _, .imp φ ψ, v, xs => by
    rw [relationalizeFormula_imp, BoundedFormulaω.realize_imp, BoundedFormulaω.realize_imp,
      realize_relationalizeFormula φ, realize_relationalizeFormula ψ]
  | _, .all φ, v, xs => by
    rw [relationalizeFormula_all, BoundedFormulaω.realize_all, BoundedFormulaω.realize_all]
    exact forall_congr' fun x => realize_relationalizeFormula φ v _
  | _, .iSup φs, v, xs => by
    rw [relationalizeFormula_iSup, BoundedFormulaω.realize_iSup, BoundedFormulaω.realize_iSup]
    exact exists_congr fun i => realize_relationalizeFormula (φs i) v xs
  | _, .iInf φs, v, xs => by
    rw [relationalizeFormula_iInf, BoundedFormulaω.realize_iInf, BoundedFormulaω.realize_iInf]
    exact forall_congr' fun i => realize_relationalizeFormula (φs i) v xs

/-! ### The nested-formula pilot: `R(f(g(x), h(c)))` -/

example (R : L.Relations 1) (f : L.Functions 2) (g h : L.Functions 1) (c : L.Functions 0)
    (x : α) (v : α → M) (xs : Fin 0 → M) :
    (relationalizeFormula (BoundedFormulaω.rel R
        ![Term.func f ![Term.func g ![Term.var (Sum.inl x)],
          Term.func h ![Term.func c Fin.elim0] ] ])).Realize v xs ↔
      RelMap R ![funMap f ![funMap g ![v x], funMap h ![funMap c Fin.elim0] ] ] := by
  rw [realize_relationalizeFormula, BoundedFormulaω.realize_rel]
  have h1 : (fun j : Fin 1 => Term.realize (M := M) (Sum.elim v xs)
      ((![Term.var (Sum.inl x)] : Fin 1 → L.Term (α ⊕ Fin 0)) j)) = ![v x] := by
    funext j
    simp [Matrix.cons_val_fin_one]
  have hc : (fun j : Fin 0 => Term.realize (M := M) (Sum.elim v xs)
      ((Fin.elim0 : Fin 0 → L.Term (α ⊕ Fin 0)) j)) = Fin.elim0 :=
    funext fun j => j.elim0
  have hcc : (fun _ : Fin 1 => funMap (M := M) c Fin.elim0) = ![funMap c Fin.elim0] :=
    funext fun j => (Matrix.cons_val_fin_one _ _ _).symm
  have hT : (fun i : Fin 1 => Term.realize (M := M) (Sum.elim v xs)
      ((![Term.func f ![Term.func g ![Term.var (Sum.inl x)],
          Term.func h ![Term.func c Fin.elim0] ] ] : Fin 1 → L.Term (α ⊕ Fin 0)) i)) =
      ![funMap f ![funMap g ![v x], funMap h ![funMap c Fin.elim0] ] ] := by
    funext i
    have hargs : (fun i : Fin 2 => Term.realize (M := M) (Sum.elim v xs)
        ((![Term.func g ![Term.var (Sum.inl x)], Term.func h ![Term.func c Fin.elim0] ] :
          Fin 2 → L.Term (α ⊕ Fin 0)) i)) =
        ![funMap g ![v x], funMap h ![funMap c Fin.elim0] ] := by
      funext i
      induction i using Fin.cases
      · simp only [Matrix.cons_val_zero, Term.realize_func, h1]
      · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, Term.realize_func, hc, hcc]
    simp only [Matrix.cons_val_fin_one, Term.realize_func, hargs]
  rw [hT]

end Semantics

/-! ## The exact occurrence identities -/

/-- The equality atom's relation symbols: exactly the graph relations of the function symbols
occurring in `t` or `u`. -/
theorem relationsIn_equalGraph (t u : L.Term (α ⊕ Fin n)) :
    (equalGraph t u).relationsIn = graphRelSym L '' (t.functionsIn ∪ u.functionsIn) := by
  rw [equalGraph, BoundedFormulaω.relationsIn_existsBlock, BoundedFormulaω.relationsIn_and,
    relationsIn_termGraphAux, relationsIn_termGraphAux]
  exact (Set.image_union _ _ _).symm

/-- The relation atom's relation symbols: exactly the relationalization of its own symbols —
the base relation `R` plus the graph relations of the arguments' function symbols. -/
theorem relationsIn_relGraph {k : ℕ} (R : L.Relations k) (ts : Fin k → L.Term (α ⊕ Fin n)) :
    (relGraph R ts).relationsIn = relSym L (⋃ i, (ts i).functionsIn) {⟨k, R⟩} := by
  rw [relGraph, BoundedFormulaω.relationsIn_existsBlock, BoundedFormulaω.relationsIn_and,
    BoundedFormulaω.relationsIn_einf,
    Set.iUnion_congr fun i => relationsIn_termGraphAux (ts i) _ _]
  show (⋃ i, graphRelSym L '' (ts i).functionsIn) ∪ {⟨k, GraphRelation.base R⟩} = _
  rw [relSym, Set.image_singleton, Set.union_comm, ← Set.image_iUnion]
  rfl

/-- **The exact occurrence identity**: the relationalized formula's relation symbols are exactly
the relationalization `relSym` of the original formula's symbols. Composes immediately with
`relSym_inter` for the sharp shared-vocabulary bound. -/
theorem relationsIn_relationalizeFormula :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n),
      (relationalizeFormula φ).relationsIn = relSym L φ.functionsIn φ.relationsIn
  | _, .falsum => (relSym_empty (L := L)).symm
  | _, .equal t u => by
    rw [relationalizeFormula_equal, relationsIn_equalGraph]
    show _ = relSym L (t.functionsIn ∪ u.functionsIn) ∅
    rw [relSym, Set.image_empty, Set.empty_union]
  | _, .rel R ts => relationsIn_relGraph R ts
  | _, .imp φ ψ => by
    rw [relationalizeFormula_imp]
    show (relationalizeFormula φ).relationsIn ∪ (relationalizeFormula ψ).relationsIn = _
    rw [relationsIn_relationalizeFormula φ, relationsIn_relationalizeFormula ψ]
    exact (relSym_union _ _ _ _).symm
  | _, .all φ => relationsIn_relationalizeFormula φ
  | _, .iSup φs => by
    rw [relationalizeFormula_iSup]
    show (⋃ i, (relationalizeFormula (φs i)).relationsIn) = _
    rw [Set.iUnion_congr fun i => relationsIn_relationalizeFormula (φs i)]
    exact (relSym_iUnion _ _).symm
  | _, .iInf φs => by
    rw [relationalizeFormula_iInf]
    show (⋃ i, (relationalizeFormula (φs i)).relationsIn) = _
    rw [Set.iUnion_congr fun i => relationsIn_relationalizeFormula (φs i)]
    exact (relSym_iUnion _ _).symm

/-- No function symbol occurs in a relationalized formula (the graph language is relational). -/
theorem functionsIn_relationalizeFormula (φ : L.BoundedFormulaω α n) :
    (relationalizeFormula φ).functionsIn = ∅ :=
  BoundedFormulaω.functionsIn_of_isRelational _

end FirstOrder.Language
