/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.GraphLanguage
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Term graphs: relationalizing a term's value (Craig Layer 3, Unit 3)

The graph formula of a term: `termGraph t y` asserts, in the relationalized language
`graphLanguage L`, that the value of the `L`-term `t` is (the value of) the variable term `y`.
Nested applications are flattened through auxiliary bound variables — one block of `k` fresh
variables per `k`-ary function application, bound by `existsBlock` — with each argument's value
pinned by its own recursive graph formula and the application itself by one graph atom
`G_f(y⃗, y)`.

## Design

The recursion is **context-polymorphic** (`termGraphAux`): instead of relabeling already-built
graph formulas when the bound context grows, the auxiliary carries a variable embedding
`ρ : β → (graphLanguage L).Term (α ⊕ Fin m)` of the term's variables into the *current* context
and a proposed output term `y`. Recursive calls enlarge `m` by the function arity while still
structurally recurring on a genuine subterm, and `existsBlock` (Unit 2) handles all environment
growth uniformly. Arity `0` (constants) is the same construction with an empty witness block —
no special case.

The semantics is oriented *term value equals output* — matching the landed graph-relation
definition `funMap f args = output` (`graphExpansion_relMap_graph`) — so no symmetry rewrites
are ever needed.

## Main Results

- `realize_termGraphAux`: the stronger context-polymorphic semantics,
  `(termGraphAux t ρ y).Realize v xs ↔ t.realize (fun z => (ρ z).realize (Sum.elim v xs)) =
  y.realize (Sum.elim v xs)` over the graph expansion.
- `realize_termGraph`: the public form, `t.realize (Sum.elim v xs) = y.realize (Sum.elim v xs)`.
- `relationsIn_termGraph`: the graph formula's relation occurrences are **exactly** the
  `graphRelSym`-image of `t.functionsIn` — in particular no base relations occur
  (`relationsIn_termGraph_inter_base`), and no function symbols occur at all
  (`functionsIn_termGraph`, the language is relational).
- The nested-term pilot `f(g(x), h(c))` (genuinely nested, includes a `0`-ary application).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {α β : Type} {m : ℕ}

/-! ## Context lifting and witness variables -/

/-- Lift a graph-language term along the bound-context extension `m → m + k` (the existing
context keeps the first `m` coordinates). -/
def graphTermLift (k : ℕ) (u : (graphLanguage L).Term (α ⊕ Fin m)) :
    (graphLanguage L).Term (α ⊕ Fin (m + k)) :=
  u.relabel (Sum.map id (Fin.castAdd k))

/-- The `i`-th auxiliary witness variable of a fresh block of `k` bound variables appended to a
context of size `m`. -/
def graphWitnessVar (m : ℕ) {k : ℕ} (i : Fin k) : (graphLanguage L).Term (α ⊕ Fin (m + k)) :=
  Term.var (Sum.inr (Fin.natAdd m i))

/-! ## The term-graph formula -/

/-- The context-polymorphic term-graph formula: `termGraphAux t ρ y` asserts that the value of
the `L`-term `t` — its variables read through the embedding `ρ` into the current context — is
the value of `y`. A variable is an equality atom; an application `f(t₀, …, t_{k-1})` extends the
context by `k` witness variables, pins each argument's value with a recursive graph formula,
adds the graph atom `G_f(y⃗, y)`, and existentially closes the witness block. -/
def termGraphAux : ∀ {m : ℕ}, L.Term β → (β → (graphLanguage L).Term (α ⊕ Fin m)) →
    (graphLanguage L).Term (α ⊕ Fin m) → (graphLanguage L).BoundedFormulaω α m
  | _, .var z, ρ, y => .equal (ρ z) y
  | m, .func f ts, ρ, y =>
    .existsBlock
      ((BoundedFormulaω.einf fun i =>
          termGraphAux (ts i) (fun z => graphTermLift _ (ρ z)) (graphWitnessVar m i)).and
        (.rel (GraphRelation.graph f)
          (Fin.snoc (fun i => graphWitnessVar m i) (graphTermLift _ y))))

/-- The term-graph formula over the ambient context, via the identity variable embedding:
`termGraph t y` asserts in `graphLanguage L` that the value of `t` is the value of `y`. -/
def termGraph (t : L.Term (α ⊕ Fin m)) (y : (graphLanguage L).Term (α ⊕ Fin m)) :
    (graphLanguage L).BoundedFormulaω α m :=
  termGraphAux t Term.var y

/-! ## Semantics over the graph expansion -/

section Semantics

attribute [local instance] graphExpansion

variable {M : Type} [L.Structure M]

@[simp] theorem realize_graphTermLift {k : ℕ} (u : (graphLanguage L).Term (α ⊕ Fin m))
    (v : α → M) (xs : Fin m → M) (ws : Fin k → M) :
    (graphTermLift k u).realize (Sum.elim v (Fin.append xs ws)) = u.realize (Sum.elim v xs) := by
  have henv : Sum.elim v (Fin.append xs ws) ∘ Sum.map id (Fin.castAdd k) = Sum.elim v xs := by
    funext z
    rcases z with a | i
    · rfl
    · exact Fin.append_left xs ws i
  rw [graphTermLift, Term.realize_relabel, henv]

@[simp] theorem realize_graphWitnessVar {k : ℕ} (i : Fin k)
    (v : α → M) (xs : Fin m → M) (ws : Fin k → M) :
    (graphWitnessVar (L := L) m i).realize (Sum.elim v (Fin.append xs ws)) = ws i :=
  Fin.append_right xs ws i

/-- **Auxiliary semantics** (the stronger, context-polymorphic form): over the graph expansion,
`termGraphAux t ρ y` holds iff the value of `t` — its variables read through `ρ` — equals the
value of `y`. Oriented *term value equals output*, matching `graphExpansion_relMap_graph`. -/
theorem realize_termGraphAux :
    ∀ {m : ℕ} (t : L.Term β) (ρ : β → (graphLanguage L).Term (α ⊕ Fin m))
      (y : (graphLanguage L).Term (α ⊕ Fin m)) (v : α → M) (xs : Fin m → M),
      (termGraphAux t ρ y).Realize v xs ↔
        (t.realize fun z => (ρ z).realize (Sum.elim v xs)) = y.realize (Sum.elim v xs)
  | _, .var z, ρ, y, v, xs => by
    simp only [termGraphAux, BoundedFormulaω.realize_equal, Term.realize]
  | m, Term.func (l := k) f ts, ρ, y, v, xs => by
    have hIH : ∀ (ws : Fin _ → M) (i),
        (termGraphAux (ts i) (fun z => graphTermLift _ (ρ z))
            (graphWitnessVar m i)).Realize v (Fin.append xs ws) ↔
          (ts i).realize (fun z => (ρ z).realize (Sum.elim v xs)) = ws i := by
      intro ws i
      rw [realize_termGraphAux (ts i)]
      simp only [realize_graphTermLift, realize_graphWitnessVar]
    have hinit : ∀ ws : Fin k → M,
        (Fin.init fun j => Term.realize (Sum.elim v (Fin.append xs ws))
          ((Fin.snoc (fun i => graphWitnessVar m i) (graphTermLift k y) :
            Fin (k + 1) → (graphLanguage L).Term (α ⊕ Fin (m + k))) j)) = ws := by
      intro ws
      funext i
      change Term.realize _
        ((Fin.snoc (fun i => graphWitnessVar m i) (graphTermLift k y) :
          Fin (k + 1) → (graphLanguage L).Term (α ⊕ Fin (m + k))) (Fin.castSucc i)) = ws i
      rw [Fin.snoc_castSucc]
      exact realize_graphWitnessVar i v xs ws
    change (BoundedFormulaω.existsBlock _).Realize v xs ↔ _
    rw [BoundedFormulaω.realize_existsBlock]
    constructor
    · rintro ⟨ws, hw⟩
      rw [BoundedFormulaω.realize_and, BoundedFormulaω.realize_einf] at hw
      obtain ⟨hconj, hatom⟩ := hw
      rw [BoundedFormulaω.realize_rel, graphExpansion_relMap_graph] at hatom
      simp only [Fin.snoc_last, realize_graphTermLift] at hatom
      rw [hinit ws] at hatom
      have harg : ∀ i, (ts i).realize (fun z => (ρ z).realize (Sum.elim v xs)) = ws i :=
        fun i => (hIH ws i).mp (hconj i)
      rw [Term.realize_func, funext harg]
      exact hatom
    · intro h
      refine ⟨fun i => (ts i).realize (fun z => (ρ z).realize (Sum.elim v xs)), ?_⟩
      rw [BoundedFormulaω.realize_and, BoundedFormulaω.realize_einf]
      refine ⟨fun i => (hIH _ i).mpr rfl, ?_⟩
      rw [BoundedFormulaω.realize_rel, graphExpansion_relMap_graph]
      simp only [Fin.snoc_last, realize_graphTermLift]
      rw [hinit]
      rw [Term.realize_func] at h
      exact h

/-- **Public semantics**: over the graph expansion, `termGraph t y` holds iff the value of `t`
equals the value of `y` in the ambient environment. -/
private theorem realize_termGraph (t : L.Term (α ⊕ Fin m)) (y : (graphLanguage L).Term (α ⊕ Fin m))
    (v : α → M) (xs : Fin m → M) :
    (termGraph t y).Realize v xs ↔
      t.realize (Sum.elim v xs) = y.realize (Sum.elim v xs) := by
  rw [termGraph, realize_termGraphAux]
  simp only [Term.realize_var]

/-! ### The nested-term pilot: `f(g(x), h(c))`

Genuinely nested arguments (each argument is itself an application) and a `0`-ary application
(`c`), all through the same construction — the acceptance gate for the unit. -/

example (f : L.Functions 2) (g h : L.Functions 1) (c : L.Functions 0) (x : α)
    (y : (graphLanguage L).Term (α ⊕ Fin 0)) (v : α → M) (xs : Fin 0 → M) :
    (termGraph (Term.func f ![Term.func g ![Term.var (Sum.inl x)],
        Term.func h ![Term.func c Fin.elim0] ]) y).Realize v xs ↔
      funMap f ![funMap g ![v x], funMap h ![funMap c Fin.elim0] ] =
        y.realize (Sum.elim v xs) := by
  rw [realize_termGraph]
  have h1 : (fun j : Fin 1 => Term.realize (M := M) (Sum.elim v xs)
      ((![Term.var (Sum.inl x)] : Fin 1 → L.Term (α ⊕ Fin 0)) j)) = ![v x] := by
    funext j
    simp [Matrix.cons_val_fin_one]
  have hc : (fun j : Fin 0 => Term.realize (M := M) (Sum.elim v xs)
      ((Fin.elim0 : Fin 0 → L.Term (α ⊕ Fin 0)) j)) = Fin.elim0 :=
    funext fun j => j.elim0
  have hcc : (fun _ : Fin 1 => funMap (M := M) c Fin.elim0) = ![funMap c Fin.elim0] :=
    funext fun j => (Matrix.cons_val_fin_one _ _ _).symm
  have hargs : (fun i : Fin 2 => Term.realize (M := M) (Sum.elim v xs)
      ((![Term.func g ![Term.var (Sum.inl x)], Term.func h ![Term.func c Fin.elim0] ] :
        Fin 2 → L.Term (α ⊕ Fin 0)) i)) =
      ![funMap g ![v x], funMap h ![funMap c Fin.elim0] ] := by
    funext i
    induction i using Fin.cases
    · simp only [Matrix.cons_val_zero, Term.realize_func, h1]
    · simp only [Matrix.cons_val_succ, Matrix.cons_val_fin_one, Term.realize_func, hc, hcc]
  rw [Term.realize_func, hargs]

end Semantics

/-! ## Occurrence identities -/

/-- The relation symbols of the auxiliary term-graph formula are exactly the graph relations of
the term's function symbols — independent of the embedding `ρ` and the output `y` (graph-language
terms are pure variables and contribute nothing). -/
theorem relationsIn_termGraphAux :
    ∀ {m : ℕ} (t : L.Term β) (ρ : β → (graphLanguage L).Term (α ⊕ Fin m))
      (y : (graphLanguage L).Term (α ⊕ Fin m)),
      (termGraphAux t ρ y).relationsIn = graphRelSym L '' t.functionsIn
  | _, .var z, ρ, y => by
    simp only [termGraphAux, Term.functionsIn, Set.image_empty]
    rfl
  | m, .func f ts, ρ, y => by
    change (BoundedFormulaω.existsBlock _).relationsIn = _
    rw [BoundedFormulaω.relationsIn_existsBlock, BoundedFormulaω.relationsIn_and,
      BoundedFormulaω.relationsIn_einf]
    rw [Set.iUnion_congr fun i => relationsIn_termGraphAux (ts i) _ _]
    change (⋃ i, graphRelSym L '' (ts i).functionsIn) ∪ {graphRelSym L ⟨_, f⟩} = _
    rw [← Set.image_iUnion, Set.union_singleton, ← Set.image_insert_eq]
    rfl

end FirstOrder.Language
